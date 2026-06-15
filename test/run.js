// Compiles the contracts with solc-js, deploys them into an in-process EVM
// (@ethereumjs/vm), runs every test vector in tests/, checks verdicts and
// produces a gas report.
'use strict';

const fs = require('fs');
const path = require('path');
const solc = require('solc');
const { ethers } = require('ethers');
const { parseNdjson, encodeForChain, KERNEL_ABI, VERDICT, REASONS } = require('../tools/lib');

const ROOT = path.join(__dirname, '..');

const { build } = require('../tools/build');

const { makeVm, installKernel, callContract: call, bytesToHex } = require('../tools/evm');

const EIP170_CODE_SIZE = 24576n;
const EIP7907_TARGET_CODE_SIZE = 65536n;
const EIP7825_TX_GAS_CAP = 16777216n;

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------
async function main() {
  console.log('compiling…');
  const artifacts = build();
  const sizeBytes = artifacts.LeanKernel.deployedSize;
  console.log(`LeanKernel deployed bytecode: ${sizeBytes} bytes ` +
    `(EIP-170: ${EIP170_CODE_SIZE}; EIP-7907/Glamsterdam target: ${EIP7907_TARGET_CODE_SIZE})`);
  if (BigInt(sizeBytes) > EIP170_CODE_SIZE) console.warn('!! exceeds EIP-170 — needs EIP-7907 (Glamsterdam) or an L2 without the limit');

  const vm = await makeVm();
  const kernelAddr = await installKernel(vm, artifacts);
  console.log(`LeanKernel installed in local EVM at ${kernelAddr.toString()}` +
    (sizeBytes > 24576 ? ' (state-injected: simulates EIP-7907/L2 deployment)' : '') + '\n');

  const iface = new ethers.Interface(KERNEL_ABI);

  const manifest = JSON.parse(fs.readFileSync(path.join(ROOT, 'tests', 'manifest.json'), 'utf8'));
  // real Lean Kernel Arena test files (all adversarial, expected: reject)
  const arenaDir = path.join(ROOT, 'tests', 'arena');
  if (fs.existsSync(arenaDir)) {
    for (const f of fs.readdirSync(arenaDir).sort()) {
      if (f.endsWith('.ndjson')) manifest.push({ group: 'arena', name: f.replace(/\.ndjson$/, '') });
    }
  }
  const expectedOf = { good: 0n, bad: 1n, decline: 2n, arena: 1n };

  let pass = 0;
  let fail = 0;
  const rows = [];

  for (const t of manifest) {
    const file = path.join(ROOT, 'tests', t.group === 'arena' ? 'arena' : t.group, `${t.name}.ndjson`);
    const parsed = parseNdjson(fs.readFileSync(file, 'utf8'));
    const enc = encodeForChain(parsed);
    const calldata = iface.encodeFunctionData('check', [
      enc.nameTab, enc.nameStrs, enc.levelTab, enc.exprTab, enc.pool, enc.declTab,
    ]);
    const r = await call(vm, kernelAddr, calldata);
    let verdict = null, failedDecl = null, reason = null, gas = r.execResult.executionGasUsed;
    if (r.execResult.exceptionError) {
      verdict = -1n;
    } else {
      [verdict, failedDecl, reason] = iface.decodeFunctionResult('check', bytesToHex(r.execResult.returnValue));
    }
    const expected = expectedOf[t.group];
    const ok = verdict === expected || (verdict !== null && BigInt(verdict) === expected);
    if (ok) pass++; else fail++;
    rows.push({
      test: `${t.group}/${t.name}`,
      expected: VERDICT[Number(expected)],
      got: verdict === -1n ? 'EVM-REVERT' : VERDICT[Number(verdict)],
      reason: verdict !== -1n && Number(verdict) !== 0
        ? `decl#${failedDecl}: ${REASONS[Number(reason)] || String(reason)}` : '',
      gas: gas.toString(),
      calldataBytes: (calldata.length - 2) / 2,
      ok,
    });
  }

  // report
  const w = (s, n) => String(s).padEnd(n);
  console.log(w('test', 34) + w('expected', 10) + w('got', 12) + w('gas', 12) + w('calldata', 10) + 'note');
  console.log('-'.repeat(96));
  for (const r of rows) {
    console.log(
      w(r.test, 34) + w(r.expected, 10) + w((r.ok ? '✓ ' : '✗ ') + r.got, 12) +
      w(r.gas, 12) + w(r.calldataBytes, 10) + r.reason
    );
  }
  console.log('-'.repeat(96));
  console.log(`${pass}/${pass + fail} tests passed`);

  // write gas report for the plan
  const maxGas = rows.reduce((acc, r) => {
    const g = BigInt(r.gas);
    return g > acc ? g : acc;
  }, 0n);
  const maxCalldataBytes = rows.reduce((acc, r) => Math.max(acc, r.calldataBytes), 0);
  fs.writeFileSync(path.join(ROOT, 'gas-report.json'), JSON.stringify({
    sourceHash: artifacts.sourceHash,
    budgets: {
      eip170CodeSize: EIP170_CODE_SIZE.toString(),
      eip7907TargetCodeSize: EIP7907_TARGET_CODE_SIZE.toString(),
      eip7825TxGasCap: EIP7825_TX_GAS_CAP.toString(),
    },
    artifacts: {
      LeanKernel: {
        deployedSize: artifacts.LeanKernel.deployedSize,
        initcodeSize: artifacts.LeanKernel.initcodeSize,
      },
      TheoremRegistry: {
        deployedSize: artifacts.TheoremRegistry.deployedSize,
        initcodeSize: artifacts.TheoremRegistry.initcodeSize,
      },
    },
    summary: {
      tests: rows.length,
      passed: pass,
      failed: fail,
      maxGas: maxGas.toString(),
      txCapHeadroomAtMaxGas: (EIP7825_TX_GAS_CAP - maxGas).toString(),
      maxCalldataBytes,
    },
    sizeBytes,
    rows,
  }, null, 2));

  if (fail > 0) process.exit(1);
}

main().catch((e) => { console.error(e); process.exit(1); });
