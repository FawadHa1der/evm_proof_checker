#!/usr/bin/env node
// Arena entry point: actual Solidity execution; 0 accept, 1 reject, 2 decline,
// 3 checker fault. Resource/format limits are shared with the corpus runner.
'use strict';

const fs = require('fs');
const { makeChecker, checkFile } = require('../tools/checker');
const { VERDICT } = require('../tools/lib');
const { DEFAULT_MAX_BYTES, DEFAULT_GAS_LIMIT, parseLimit, parseByteLimit } = require('../tools/budgets');

async function main() {
  const file = process.argv[2] || process.env.IN;
  if (!file) throw new Error('usage: evmlean.js <export.ndjson> (or set $IN)');
  const maxBytes = parseByteLimit(process.env.EVMLEAN_MAX_BYTES ?? DEFAULT_MAX_BYTES, 'EVMLEAN_MAX_BYTES');
  const gasLimit = parseLimit(process.env.EVMLEAN_GAS ?? DEFAULT_GAS_LIMIT, 'EVMLEAN_GAS');
  if (maxBytes && fs.statSync(file).size > maxBytes) {
    console.error('evmlean: export exceeds EVMLEAN_MAX_BYTES=' + maxBytes + '; declining');
    process.exitCode = 2;
    return;
  }
  const result = await checkFile(file, await makeChecker(), { maxBytes, gasLimit });
  console.error('evmlean: ' + VERDICT[result.verdict] + ' (decl ' + result.failedDecl + ', '
    + result.reason + '); gas=' + result.gas + '; ' + result.category);
  process.exitCode = result.verdict;
}

main().catch((error) => { console.error(error.message || error); process.exitCode = 3; });
