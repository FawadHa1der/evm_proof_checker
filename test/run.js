// Compiles the contracts with solc-js, deploys them into an in-process EVM
// (@ethereumjs/vm), runs every test vector in tests/, checks verdicts and
// produces a gas report.
'use strict';

const fs = require('fs');
const path = require('path');
const { createHash } = require('crypto');
const { ethers } = require('ethers');
const { parseNdjson, encodeForChain, KERNEL_ABI, VERDICT, REASONS } = require('../tools/lib');

const ROOT = path.join(__dirname, '..');

const { build } = require('../tools/build');

const { makeVm, installKernel, callContract: call, bytesToHex } = require('../tools/evm');
const { validateOutcome } = require('../tools/fetch-arena-tests');
const { outcomeMatches } = require('../tools/checker');
const { CODE_SIZE_LIMIT, INITCODE_SIZE_LIMIT, EXECUTION_GAS_CAP, MODEL, transactionBudget } = require('../tools/budgets');

const EIP170_CODE_SIZE = 24576n;
const EIP7954_TARGET_CODE_SIZE = BigInt(CODE_SIZE_LIMIT);
const EIP7825_TX_GAS_CAP = EXECUTION_GAS_CAP;

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------
async function main() {
  console.log('compiling…');
  const artifacts = build();
  const sizeBytes = artifacts.LeanKernel.deployedSize;
  console.log(`LeanKernel deployed bytecode: ${sizeBytes} bytes ` +
    `(EIP-170: ${EIP170_CODE_SIZE}; EIP-7954/Glamsterdam target: ${EIP7954_TARGET_CODE_SIZE})`);
  if (sizeBytes > CODE_SIZE_LIMIT || artifacts.LeanKernel.initcodeSize > INITCODE_SIZE_LIMIT) {
    throw new Error('LeanKernel exceeds the EIP-7954 code/initcode target');
  }
  if (BigInt(sizeBytes) > EIP170_CODE_SIZE) console.warn('!! exceeds EIP-170; deployment requires a chain with raised limits');

  const vm = await makeVm();
  const kernelAddr = await installKernel(vm, artifacts);
  console.log(`LeanKernel installed in local EVM at ${kernelAddr.toString()}` +
    (sizeBytes > 24576 ? ' (state-injected; NOT a deployment or full Glamsterdam simulation)' : '') + '\n');

  const iface = new ethers.Interface(KERNEL_ABI);

  const manifest = JSON.parse(fs.readFileSync(path.join(ROOT, 'tests', 'manifest.json'), 'utf8'));
  // Real Lean Kernel Arena test files. The expected verdict is the Arena's
  // own `outcome:` from the companion .yaml, not an assumption on our part —
  // the static tests are mostly adversarial but not all of them are
  // (level-index-out-of-order and sparse-name-index must accept).
  const arenaDir = path.join(ROOT, 'tests', 'arena');
  if (fs.existsSync(arenaDir)) {
    for (const f of fs.readdirSync(arenaDir, { recursive: true }).sort()) {
      if (!f.endsWith('.ndjson')) continue;
      const name = f.replace(/\.ndjson$/, '');
      const yml = path.join(arenaDir, `${name}.yaml`);
      if (!fs.existsSync(yml)) {
        throw new Error(`tests/arena/${name}.ndjson has no ${name}.yaml declaring its outcome; `
          + 're-run tools/fetch-arena-tests.sh');
      }
      const outcome = validateOutcome(fs.readFileSync(yml, 'utf8'), yml);
      manifest.push({ group: 'arena', name, outcome });
    }
  }
  const upstreamManifest = path.join(ROOT, 'tests', 'upstream', 'manifest.json');
  if (fs.existsSync(upstreamManifest)) {
    const upstream = JSON.parse(fs.readFileSync(upstreamManifest, 'utf8'));
    for (const entry of upstream.tests) manifest.push({ ...entry, group: 'upstream' });
    for (const alias of upstream.aliases || []) {
      const bytes = fs.readFileSync(path.join(ROOT, alias.coveredBy));
      if (createHash('sha256').update(bytes).digest('hex') !== alias.sha256) {
        throw new Error(`upstream alias no longer byte-identical: ${alias.name} -> ${alias.coveredBy}`);
      }
    }
  }
  // nested-inductive ground truth (byte-real lean4export output); files named
  // reject-* are adversarial and must reject, the rest must accept
  const nestedDir = path.join(ROOT, 'tests', 'nested');
  if (fs.existsSync(nestedDir)) {
    for (const f of fs.readdirSync(nestedDir).sort()) {
      if (f.endsWith('.ndjson')) {
        manifest.push({
          group: f.startsWith('reject-') ? 'nested-reject' : 'nested',
          name: f.replace(/\.ndjson$/, ''),
        });
      }
    }
  }
  // byte-real lean4export fixtures for defeq/reduction corners that our
  // hand-built vectors cannot express; same reject-* naming convention
  const leanDir = path.join(ROOT, 'tests', 'lean');
  if (fs.existsSync(leanDir)) {
    for (const f of fs.readdirSync(leanDir).sort()) {
      if (f.endsWith('.ndjson')) {
        manifest.push({
          group: f.startsWith('reject-') ? 'lean-reject' : 'lean',
          name: f.replace(/\.ndjson$/, ''),
        });
      }
    }
  }
  const expectedOf = {
    good: 0n, bad: 1n, decline: 2n, arena: 1n, 'arena-accept': 0n,
    nested: 0n, 'nested-reject': 1n, lean: 0n, 'lean-reject': 1n,
  };
  const dirOf = (g) => {
    if (g === 'nested' || g === 'nested-reject') return 'nested';
    if (g === 'lean' || g === 'lean-reject') return 'lean';
    if (g === 'arena-accept') return 'arena';
    return g;
  };

  let pass = 0;
  let fail = 0;
  const rows = [];
  let eitherChecked = 0;

  for (const t of manifest) {
    const file = path.join(ROOT, 'tests', dirOf(t.group), `${t.name}.ndjson`);
    const text = fs.readFileSync(file, 'utf8');
    if (t.sha256 && createHash('sha256').update(text).digest('hex') !== t.sha256) {
      throw new Error(`fixture checksum mismatch: ${file}`);
    }
    const parsed = parseNdjson(text);
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
    const expected = t.outcome || VERDICT[Number(expectedOf[t.group])];
    const budget = transactionBudget(calldata, gas);
    const ok = outcomeMatches(expected, Number(verdict))
      && (!t.requireTransactionFit || budget.fitsTransaction);
    if (ok) pass++; else fail++;
    if (ok && expected === 'either') eitherChecked++;
    rows.push({
      test: `${t.group}/${t.name}`,
      expected,
      got: verdict === -1n ? 'EVM-REVERT' : VERDICT[Number(verdict)],
      reason: verdict !== -1n && Number(verdict) !== 0
        ? `decl#${failedDecl}: ${REASONS[Number(reason)] || String(reason)}` : '',
      gas: gas.toString(),
      calldataBytes: (calldata.length - 2) / 2,
      budget: JSON.parse(JSON.stringify(budget, (_, v) => typeof v === 'bigint' ? String(v) : v)),
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
  console.log(`${eitherChecked} of these are unscored either-outcome checks, not soundness/completeness results.`);
  const candidates = rows.filter(r => r.ok && ['accept', 'reject'].includes(r.got) && r.budget.fitsTransaction).length;
  console.log(`${candidates}/${rows.length} fit the ${MODEL} direct-call estimate (including calldata); not deployment evidence.`);

  // write gas report for the plan
  const maxGas = rows.reduce((acc, r) => {
    const g = BigInt(r.gas);
    return g > acc ? g : acc;
  }, 0n);
  const maxCalldataBytes = rows.reduce((acc, r) => Math.max(acc, r.calldataBytes), 0);
  fs.writeFileSync(path.join(ROOT, 'gas-report.json'), JSON.stringify({
    sourceHash: artifacts.sourceHash,
    compiler: artifacts.compiler,
    executionModel: 'Cancun EVM with state-injected runtime code',
    budgets: {
      eip170CodeSize: EIP170_CODE_SIZE.toString(),
      eip7954TargetCodeSize: EIP7954_TARGET_CODE_SIZE.toString(),
      eip7954TargetInitcodeSize: INITCODE_SIZE_LIMIT.toString(),
      eip7825TxGasCap: EIP7825_TX_GAS_CAP.toString(),
      transactionModel: MODEL,
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
      eitherChecked,
      transactionCandidates: candidates,
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
