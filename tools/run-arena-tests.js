#!/usr/bin/env node
// Run a downloaded Lean Kernel Arena test tarball/directory against the
// Solidity checker using one in-process EVM instance.
'use strict';

const fs = require('fs');
const path = require('path');
const { ethers } = require('ethers');
const { parseNdjson, encodeForChain, KERNEL_ABI, VERDICT, REASONS } = require('./lib');
const { build } = require('./build');
const { makeVm, installKernel, callContract, bytesToHex } = require('./evm');

function usage() {
  console.error(
    [
      'usage: node tools/run-arena-tests.js <arena-test-dir> [options]',
      '',
      'Options:',
      '  --tutorial                     run only tutorial/* tests',
      '  --include=<regex>              run only paths matching regex',
      '  --max-bytes=<n>                skip files larger than n bytes',
      '  --entrypoint-max-bytes=<n>     simulate bin/evmlean.js size-decline guard (0 disables)',
      '  --allow-decline                count explicit decline as ok',
      '  --allow-non-tutorial-decline   count decline as ok outside tutorial/*',
      '',
      'The directory must contain Arena-style good/ and bad/ subdirectories.',
    ].join('\n')
  );
}

function parseArgs(argv) {
  const opts = {
    root: null,
    tutorial: false,
    include: null,
    maxBytes: null,
    entrypointMaxBytes: null,
    allowDecline: false,
    allowNonTutorialDecline: false,
  };
  for (const arg of argv) {
    if (arg === '--help' || arg === '-h') {
      usage();
      process.exit(0);
    } else if (arg === '--tutorial') {
      opts.tutorial = true;
    } else if (arg.startsWith('--include=')) {
      opts.include = new RegExp(arg.slice('--include='.length));
    } else if (arg.startsWith('--max-bytes=')) {
      opts.maxBytes = Number(arg.slice('--max-bytes='.length));
      if (!Number.isSafeInteger(opts.maxBytes) || opts.maxBytes < 0) {
        throw new Error('invalid --max-bytes value');
      }
    } else if (arg.startsWith('--entrypoint-max-bytes=')) {
      opts.entrypointMaxBytes = Number(arg.slice('--entrypoint-max-bytes='.length));
      if (!Number.isSafeInteger(opts.entrypointMaxBytes) || opts.entrypointMaxBytes < 0) {
        throw new Error('invalid --entrypoint-max-bytes value');
      }
    } else if (arg === '--allow-decline') {
      opts.allowDecline = true;
    } else if (arg === '--allow-non-tutorial-decline') {
      opts.allowNonTutorialDecline = true;
    } else if (!opts.root) {
      opts.root = arg;
    } else {
      throw new Error(`unknown argument: ${arg}`);
    }
  }
  if (!opts.root) throw new Error('missing arena-test-dir');
  opts.root = path.resolve(opts.root);
  return opts;
}

function walk(dir, out = []) {
  for (const ent of fs.readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, ent.name);
    if (ent.isDirectory()) walk(p, out);
    else if (p.endsWith('.ndjson')) out.push(p);
  }
  return out;
}

function selectFiles(opts) {
  const files = [];
  for (const group of ['good', 'bad']) {
    const dir = path.join(opts.root, group);
    if (!fs.existsSync(dir)) continue;
    for (const file of walk(dir)) {
      const rel = path.relative(opts.root, file);
      if (opts.tutorial && !rel.includes(`${path.sep}tutorial${path.sep}`)) continue;
      if (opts.include && !opts.include.test(rel)) continue;
      if (opts.maxBytes !== null && fs.statSync(file).size > opts.maxBytes) continue;
      files.push(file);
    }
  }
  return files.sort();
}

async function verdictForFile(file, iface, vm, kernelAddr) {
  let enc;
  try {
    const parsed = parseNdjson(fs.readFileSync(file, 'utf8'));
    const ver = parsed.meta && parsed.meta.format && parsed.meta.format.version;
    if (!ver || !String(ver).startsWith('3.')) {
      return { verdict: 2, failedDecl: 0n, reason: 'unsupported export format', gas: 0n };
    }
    enc = encodeForChain(parsed);
  } catch (e) {
    return { verdict: 2, failedDecl: 0n, reason: `encode: ${e.message}`, gas: 0n };
  }

  const calldata = iface.encodeFunctionData('check', [
    enc.nameTab, enc.nameStrs, enc.levelTab, enc.exprTab, enc.pool, enc.declTab,
  ]);
  const r = await callContract(vm, kernelAddr, calldata);
  const gas = r.execResult.executionGasUsed;
  if (r.execResult.exceptionError) {
    return { verdict: 99, failedDecl: 0n, reason: r.execResult.exceptionError.error, gas };
  }
  const [verdict, failedDecl, reason] = iface.decodeFunctionResult('check', bytesToHex(r.execResult.returnValue));
  return {
    verdict: Number(verdict),
    failedDecl,
    reason: REASONS[Number(reason)] || String(reason),
    gas,
  };
}

function isTutorial(rel) {
  return rel.includes(`${path.sep}tutorial${path.sep}`) || rel.includes('/tutorial/');
}

function sizeDeclineForFile(file, limit) {
  if (limit === null || limit === 0) return null;
  const size = fs.statSync(file).size;
  if (size <= limit) return null;
  return {
    verdict: 2,
    failedDecl: 0n,
    reason: `entrypoint size guard (${size} > ${limit} bytes)`,
    gas: 0n,
  };
}

async function main() {
  const opts = parseArgs(process.argv.slice(2));
  const files = selectFiles(opts);
  if (files.length === 0) throw new Error('no .ndjson files selected');

  const artifacts = build();
  const vm = await makeVm();
  const kernelAddr = await installKernel(vm, artifacts);
  const iface = new ethers.Interface(KERNEL_ABI);

  let exact = 0;
  let declinedOk = 0;
  let failed = 0;
  const failures = [];
  const rows = [];

  for (const file of files) {
    const rel = path.relative(opts.root, file);
    const expected = rel.startsWith(`good${path.sep}`) || rel.startsWith('good/') ? 0 : 1;
    const res = sizeDeclineForFile(file, opts.entrypointMaxBytes)
      || await verdictForFile(file, iface, vm, kernelAddr);
    const got = res.verdict;
    const declineOk = got === 2
      && (opts.allowDecline || (opts.allowNonTutorialDecline && !isTutorial(rel)));
    const ok = got === expected || declineOk;
    if (got === expected) exact++;
    else if (declineOk) declinedOk++;
    else {
      failed++;
      failures.push({
        test: rel,
        expected: VERDICT[expected],
        got: VERDICT[got] || String(got),
        gas: String(res.gas),
        reason: `decl#${res.failedDecl}: ${res.reason}`,
      });
    }
    rows.push({ rel, expected, got, ok, gas: res.gas, failedDecl: res.failedDecl, reason: res.reason });
  }

  const totalGas = rows.reduce((acc, r) => acc + r.gas, 0n);
  console.log(`arena tests: ${files.length} selected, ${exact} exact, ${declinedOk} declined-ok, ${failed} failed`);
  console.log(`total gas used in local EVM calls: ${totalGas}`);
  if (failures.length) {
    console.log('\nfailures:');
    for (const f of failures.slice(0, 50)) {
      console.log(`${f.test}: expected ${f.expected}, got ${f.got}, gas ${f.gas}, ${f.reason}`);
    }
    if (failures.length > 50) console.log(`... ${failures.length - 50} more`);
  }
  if (failed > 0) process.exit(1);
}

main().catch((e) => {
  console.error(e.message || e);
  process.exit(1);
});
