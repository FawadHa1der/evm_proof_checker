'use strict';

const assert = require('node:assert/strict');
const { test } = require('node:test');
const fs = require('fs');
const os = require('os');
const path = require('path');
const { spawnSync } = require('child_process');
const { ethers } = require('ethers');
const { KERNEL_ABI, parseNdjson, encodeForChain } = require('../tools/lib');
const { callContract } = require('../tools/evm');
const { transactionBudget, EXECUTION_GAS_CAP, parseLimit, parseByteLimit } = require('../tools/budgets');
const { outcomeMatches, normalizeResult, makeChecker, checkFile } = require('../tools/checker');
const { parseArgs, selectFiles } = require('../tools/run-arena-tests');
const { validateOutcome } = require('../tools/fetch-arena-tests');
const { safeRelative, validateCoverage } = require('../tools/import-arena-tests');
const iface = new ethers.Interface(KERNEL_ABI);

test('either means accept or reject, never resource exhaustion or a crash', () => {
  for (const v of [0, 1]) assert.equal(outcomeMatches('either', v), true);
  for (const v of [2, 3, 99]) assert.equal(outcomeMatches('either', v), false);
  assert.equal(outcomeMatches('accept', 1), false);
  assert.equal(outcomeMatches('reject', 0), false);
  assert.throws(() => outcomeMatches('typo', 0), /unknown/);
});

test('upstream YAML outcomes and import paths are validated structurally', () => {
  assert.equal(validateOutcome('description: |\n  outcome: reject\noutcome: "either"\n', 'fixture'), 'either');
  for (const text of ['description: missing', 'outcome: typo', 'outcome: [accept]', 'outcome: accept\noutcome: reject']) {
    assert.throws(() => validateOutcome(text, 'fixture'));
  }
  assert.equal(safeRelative('either/corner-cases/example.ndjson'), 'either/corner-cases/example.ndjson');
  for (const name of ['../escape.ndjson', '/good/a.ndjson', 'good/../../a.ndjson', 'good/./a.ndjson', 'good/a.yaml', 'good/a\\b.ndjson']) {
    assert.throws(() => safeRelative(name));
  }
  const a = { rel: 'good/a.ndjson' }, b = { rel: 'either/b.ndjson' };
  assert.doesNotThrow(() => validateCoverage([a, b], [b, a]));
  assert.throws(() => validateCoverage([a], [a, b]), /every corpus file/);
  assert.throws(() => validateCoverage([a, a], [a, b]), /every corpus file/);
});

test('draft direct-call costs include standard calldata gas and the 64/64 floor', () => {
  const b = transactionBudget('0x0001', 1000n);
  assert.equal(b.intrinsicGas, 15020n);
  assert.equal(b.calldataFloorGas, 15128n);
  assert.equal(b.estimatedTransactionGas, 16020n);
  assert.equal(b.executionAllowance, EXECUTION_GAS_CAP - 15020n);
  assert.equal(transactionBudget('0x0001').estimatedTransactionGas, 15128n);
  assert.equal(transactionBudget('0x0101').calldataFloorGas, 15128n);
  assert.throws(() => transactionBudget('0x0'), /invalid/);
});

test('execution and calldata limits are independent, with inclusive boundaries', () => {
  assert.equal(transactionBudget('0x', EXECUTION_GAS_CAP - 15000n).fitsTransaction, true);
  assert.equal(transactionBudget('0x', EXECUTION_GAS_CAP - 14999n).fitsTransaction, false);
  const max = Number((EXECUTION_GAS_CAP - 15000n) / 64n);
  assert.equal(transactionBudget('0x' + '00'.repeat(max)).fitsTransaction, true);
  assert.equal(transactionBudget('0x' + '00'.repeat(max + 1)).fitsTransaction, false);
});

test('resource exits are declines; genuine EVM faults remain faults', () => {
  for (const error of ['out of gas', 'stack overflow', 'revert', 'invalid opcode']) {
    const res = normalizeResult({ execResult: { executionGasUsed: 100n, exceptionError: { error } } }, iface);
    assert.equal(res.verdict, ['out of gas', 'stack overflow'].includes(error) ? 2 : 3);
  }
  for (const v of [0, 1, 2, 3]) {
    const data = iface.encodeFunctionResult('check', [v, 7, 1]);
    const res = normalizeResult({ execResult: { executionGasUsed: 10n, returnValue: ethers.getBytes(data) } }, iface);
    assert.equal(res.verdict, v === 3 ? 2 : v);
    assert.equal(res.failedDecl, 7n);
  }
  assert.throws(() => normalizeResult({ execResult: { executionGasUsed: 0n, returnValue: new Uint8Array() } }, iface));
});

test('invalid environment and runner budgets cannot silently disable guards', () => {
  for (const v of ['NaN', 'Infinity', '-1', '1.5', '', '1e9']) {
    assert.throws(() => parseByteLimit(v, 'bytes'));
    assert.throws(() => parseLimit(v, 'gas'));
  }
  assert.equal(parseByteLimit('0', 'bytes'), 0);
  assert.throws(() => parseLimit('0', 'gas'));
  assert.throws(() => parseByteLimit('9007199254740992', 'bytes'));
  const opts = parseArgs(['.', '--entrypoint-max-bytes=512000', '--max-bytes=500', '--gas-limit=123', '--profile=glamsterdam']);
  assert.equal(opts.entrypointMaxBytes, 512000);
  assert.equal(opts.maxBytes, 500);
  assert.equal(opts.gasLimit, 123n);
  assert.throws(() => parseArgs(['.', '--profile=wrong']));
  assert.throws(() => parseArgs(['--typo']));
});

test('runner discovers either fixtures and reports size skips', (t) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'evmlean-selection-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  for (const group of ['good', 'bad', 'either']) {
    fs.mkdirSync(path.join(root, group));
    fs.writeFileSync(path.join(root, group, 'a.ndjson'), '{}\n');
  }
  const all = selectFiles(parseArgs([root]));
  assert.equal(all.selected.length, 3);
  assert.deepEqual(new Set(all.selected.map(x => x.expected)), new Set(['accept', 'reject', 'either']));
  const skipped = selectFiles(parseArgs([root, '--max-bytes=1']));
  assert.equal(skipped.selected.length, 0);
  assert.equal(skipped.skipped.length, 3);
});

test('entry point and corpus helper agree on malformed input and low gas', async (t) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'evmlean-exits-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const bad = path.join(root, 'malformed.ndjson');
  fs.writeFileSync(bad, '{not json}\n');
  const checker = await makeChecker();
  assert.equal((await checkFile(bad, checker)).verdict, 2);
  const cli = path.join(__dirname, '../bin/evmlean.js');
  const run = (file, extra = {}) => spawnSync(process.execPath, [cli, file], {
    env: { ...process.env, EVMLEAN_MAX_BYTES: '512000', EVMLEAN_GAS: '100000000', ...extra },
    encoding: 'utf8', timeout: 30000,
  });
  assert.equal(run(bad).status, 2);
  const good = path.join(__dirname, '../tests/good/001_basicDef.ndjson');
  assert.equal(run(good).status, 0);
  assert.equal(run(good, { EVMLEAN_GAS: '100' }).status, 2);
  assert.equal((await checkFile(good, checker, { gasLimit: 100n })).verdict, 2);
  assert.equal(run(good, { EVMLEAN_MAX_BYTES: '1' }).status, 2);
  assert.equal(run(good, { EVMLEAN_MAX_BYTES: 'NaN' }).status, 3);
  assert.equal(run(path.join(root, 'missing.ndjson')).status, 3);
});

test('draft profile distinguishes file size, calldata floor, code size, and execution gas', async (t) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'evmlean-budgets-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const good = path.join(__dirname, '../tests/good/001_basicDef.ndjson');
  const checker = await makeChecker();
  const accepted = await checkFile(good, checker, { profile: 'glamsterdam' });
  assert.equal(accepted.verdict, 0);
  assert.equal(accepted.budget.fitsTransaction, true);
  assert.equal((await checkFile(good, checker, { profile: 'glamsterdam', gasLimit: 100n })).category, 'evm-resource');
  assert.equal((await checkFile(good, checker, { profile: 'glamsterdam', maxBytes: 1 })).category, 'size');
  const large = path.join(root, 'large-name.ndjson');
  const lines = fs.readFileSync(good, 'utf8').trim().split('\n').map(JSON.parse);
  lines.find(x => x.str).str.str = 'a'.repeat(270000);
  fs.writeFileSync(large, lines.map(x => JSON.stringify(x)).join('\n') + '\n');
  const noExecution = { ...checker, vm: null };
  const floor = await checkFile(large, noExecution, { profile: 'glamsterdam', maxBytes: 512000 });
  assert.equal(floor.category, 'calldata');
  assert.equal(floor.gas, 0n);
  assert.equal(floor.bytes < 512000, true);
  const oversized = { ...noExecution, artifacts: { LeanKernel: { deployedSize: 65537, initcodeSize: 65537 } } };
  assert.equal((await checkFile(good, oversized, { profile: 'glamsterdam' })).category, 'code-size');
});

test('unknown packed universe-level tags reject before recursive checking', async () => {
  const checker = await makeChecker();
  const base = encodeForChain(parseNdjson(fs.readFileSync(path.join(__dirname, '../tests/good/050_struct.ndjson'), 'utf8')));
  for (const tag of [5n, 255n]) {
    for (const payload of [0n, 1n, 999999n]) {
      const levels = [...base.levelTab];
      levels[1] = (tag << 248n) | payload;
      const cd = checker.iface.encodeFunctionData('check', [
        base.nameTab, base.nameStrs, levels, base.exprTab, base.pool, base.declTab,
      ]);
      const raw = await callContract(checker.vm, checker.kernelAddr, cd, 1000000n);
      assert.equal(raw.execResult.exceptionError, undefined, `tag ${tag}, payload ${payload}`);
      const [verdict, , reason] = checker.iface.decodeFunctionResult('check', raw.execResult.returnValue);
      assert.equal(verdict, 1n, `tag ${tag}, payload ${payload}`);
      assert.equal(reason, 29n);
    }
  }
});
