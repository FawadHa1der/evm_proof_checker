#!/usr/bin/env node
// evmlean — Lean Kernel Arena-style checker entry point backed by the EVM.
//
// Usage:   evmlean.js <export.ndjson>     (or set $IN, as the Arena does)
// Reads a lean4export NDJSON (v3.x) file, re-encodes it (pure format
// translation), executes the LeanKernel contract in an in-process EVM, and
// exits with the Arena convention:
//   0 = accepted, 1 = rejected, 2 = declined, 3+ = checker error
'use strict';

const fs = require('fs');
const { ethers } = require('ethers');
const { parseNdjson, encodeForChain, KERNEL_ABI, VERDICT, REASONS } = require('../tools/lib');
const { build } = require('../tools/build');
const { makeVm, installKernel, callContract, bytesToHex } = require('../tools/evm');

async function main() {
  const file = process.argv[2] || process.env.IN;
  if (!file) {
    console.error('usage: evmlean.js <export.ndjson>   (or set $IN)');
    process.exit(3);
  }
  const maxBytes = process.env.EVMLEAN_MAX_BYTES === '0'
    ? 0
    : Number(process.env.EVMLEAN_MAX_BYTES || 128000);
  const stat = fs.statSync(file);
  if (maxBytes > 0 && stat.size > maxBytes) {
    console.error(`evmlean: export is ${stat.size} bytes, above EVMLEAN_MAX_BYTES=${maxBytes}; declining`);
    process.exit(2);
  }
  const text = fs.readFileSync(file, 'utf8');
  const parsed = parseNdjson(text);

  // Unknown/major-incompatible format versions → decline, per Arena semantics.
  const ver = parsed.meta && parsed.meta.format && parsed.meta.format.version;
  if (!ver || !String(ver).startsWith('3.')) {
    console.error(`evmlean: unsupported export format version ${ver}; declining`);
    process.exit(2);
  }

  let enc;
  try {
    enc = encodeForChain(parsed);
  } catch (e) {
    console.error('evmlean: cannot encode export (declining):', e.message);
    process.exit(2);
  }

  const artifacts = build();
  const vm = await makeVm();
  const kernelAddr = await installKernel(vm, artifacts);

  const iface = new ethers.Interface(KERNEL_ABI);
  const calldata = iface.encodeFunctionData('check', [
    enc.nameTab, enc.nameStrs, enc.levelTab, enc.exprTab, enc.pool, enc.declTab,
  ]);
  const gasLimit = process.env.EVMLEAN_GAS ? BigInt(process.env.EVMLEAN_GAS) : undefined;
  const r = gasLimit === undefined
    ? await callContract(vm, kernelAddr, calldata)
    : await callContract(vm, kernelAddr, calldata, gasLimit);
  if (r.execResult.exceptionError) {
    const err = String(r.execResult.exceptionError.error);
    // Running out of our own gas or EVM stack is resource exhaustion — the
    // Arena's "checker gave up", which is a decline. Only a genuine fault
    // (revert, bad opcode) is a checker bug worth exit 3.
    if (err === 'out of gas' || err === 'stack overflow') {
      console.error(`evmlean: EVM resource exhaustion (${err}); declining`);
      process.exit(2);
    }
    console.error('evmlean: EVM exception:', err);
    process.exit(3);
  }
  const [verdict, failedDecl, reason] = iface.decodeFunctionResult('check', bytesToHex(r.execResult.returnValue));
  const v = Number(verdict);
  console.error(
    `evmlean: ${VERDICT[v]} (decl ${failedDecl}, ${REASONS[Number(reason)] || reason}); ` +
    `gas=${r.execResult.executionGasUsed}`
  );
  if (v === 3) {
    console.error('evmlean: contract resource budget exhausted; declining');
    process.exit(2);
  }
  process.exit(v);
}

main().catch((e) => { console.error(e); process.exit(3); });
