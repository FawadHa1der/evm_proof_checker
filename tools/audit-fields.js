#!/usr/bin/env node
// Exhaustive field-level trust audit.
//
// tools/fuzz.js mutates exports at random. This walks the encoded form
// *systematically*: every declaration record, every packed field of that
// record, every pool window it points at, against a fixed ladder of adversarial
// values. The space is finite, so the sweep is complete rather than sampled.
//
// Every soundness hole found in this kernel so far lived in a redundant
// serialised field or an unchecked index, so this is the shape of audit that
// actually finds them. Two verdicts are reported:
//
//   FAULT  — EVM revert / exception. Always a bug: the Arena reads exit 3 as
//            "this checker is broken". Resource limits must decline instead.
//   ACCEPT — the mutant still checks. Needs review: a mutation can be
//            meaning-preserving (an unused field), but it can also be a lie the
//            kernel believed.
//
//   node tools/audit-fields.js [--file=tests/good/050_struct.ndjson] [--quiet]
'use strict';

const fs = require('fs');
const path = require('path');
const { ethers } = require('ethers');
const { parseNdjson, encodeForChain, KERNEL_ABI, VERDICT, REASONS } = require('./lib');
const { build } = require('./build');
const { makeVm, installKernel, callContract, bytesToHex } = require('./evm');

const args = process.argv.slice(2);
const opt = (n, d) => {
  const a = args.find((x) => x.startsWith(`--${n}=`));
  return a ? a.slice(n.length + 3) : d;
};
const QUIET = args.includes('--quiet');

const F = (1n << 48n) - 1n;

// decl word0: kind<<248 | name | type<<48 | value<<96 | lpStart<<144 | lpLen<<192
const WORD0 = [
  ['name', 0n], ['type', 48n], ['value', 96n], ['lpStart', 144n], ['lpLen', 192n],
];
// decl word1, per kind (see LeanKernel.sol "decl kinds")
const WORD1 = {
  1: [['height', 0n]],                                             // D_DEF
  4: [['quotKind', 0n]],                                           // D_QUOT
  5: [['nT', 0n], ['nC', 48n], ['nR', 96n]],                       // D_GROUP
  6: [['numParams', 0n], ['numIndices', 48n], ['ctorsPtr', 96n], ['numNested', 144n]], // D_IND
  7: [['induct', 0n], ['cidx', 48n], ['numParams', 96n], ['numFields', 144n]],         // D_CTOR
  8: [['recParams', 0n], ['recIndices', 48n], ['numMotives', 96n], ['numMinors', 144n], ['rulesPtr', 192n]], // D_REC
};
const KINDNAME = {
  0: 'axiom', 1: 'def', 2: 'thm', 3: 'opaque', 4: 'quot',
  5: 'group', 6: 'ind', 7: 'ctor', 8: 'rec', 9: 'unsup',
};

// adversarial ladder: zero, off-by-one either way, and far out of range
const LADDER = (cur) => {
  const out = new Set(['0', '1', String(cur + 1n), '999999', String(F)]);
  if (cur > 0n) out.add(String(cur - 1n));
  out.delete(String(cur)); // skip the no-op
  return [...out].map(BigInt);
};

function cloneEnc(e) {
  return {
    nameTab: [...e.nameTab], nameStrs: e.nameStrs, levelTab: [...e.levelTab],
    exprTab: [...e.exprTab], pool: [...e.pool], declTab: [...e.declTab],
  };
}

async function main() {
  const file = opt('file', 'tests/good/050_struct.ndjson');
  const src = fs.readFileSync(path.isAbsolute(file) ? file : path.join(__dirname, '..', file), 'utf8');
  const base = encodeForChain(parseNdjson(src));

  const vm = await makeVm();
  const addr = await installKernel(vm, build());
  const iface = new ethers.Interface(KERNEL_ABI);

  async function run(enc) {
    const cd = iface.encodeFunctionData('check', [
      enc.nameTab, enc.nameStrs, enc.levelTab, enc.exprTab, enc.pool, enc.declTab,
    ]);
    let r;
    try { r = await callContract(vm, addr, cd); }
    catch (e) { return { v: 'FAULT', reason: 'throw: ' + String(e.message).slice(0, 60) }; }
    if (r.execResult.exceptionError) return { v: 'FAULT', reason: r.execResult.exceptionError.error };
    const [v, d, reason] = iface.decodeFunctionResult('check', bytesToHex(r.execResult.returnValue));
    return { v: VERDICT[Number(v)], decl: Number(d), reason: REASONS[Number(reason)] || String(reason) };
  }

  const sane = await run(base);
  if (sane.v !== 'accept') {
    console.error(`baseline ${file} is not accepted (${sane.v}: ${sane.reason}) — pick another --file`);
    process.exit(2);
  }

  const faults = [];
  const accepts = [];
  let n = 0;

  // --- declaration record fields -------------------------------------------
  const nDecls = base.declTab.length / 2;
  for (let i = 0; i < nDecls; i++) {
    const kind = Number(base.declTab[2 * i] >> 248n);
    const fields = [
      ...WORD0.map(([nm, sh]) => [nm, sh, 2 * i]),
      ...(WORD1[kind] || []).map(([nm, sh]) => [nm, sh, 2 * i + 1]),
    ];
    for (const [nm, shift, word] of fields) {
      const cur = (base.declTab[word] >> shift) & F;
      for (const val of LADDER(cur)) {
        const enc = cloneEnc(base);
        enc.declTab[word] = (enc.declTab[word] & ~(F << shift)) | (val << shift);
        const res = await run(enc);
        n++;
        const label = `decl#${i}(${KINDNAME[kind]}).${nm} = ${val}`;
        if (res.v === 'FAULT') faults.push(`${label}  -> FAULT ${res.reason}`);
        else if (res.v === 'accept') accepts.push(`${label}  -> accept`);
      }
    }
  }

  // --- pool entries (level-param lists, ctor name lists, recursor rules) ----
  for (let p = 0; p < base.pool.length; p++) {
    for (const val of [0n, base.pool[p] + 1n, 999999n]) {
      if (val === base.pool[p]) continue;
      const enc = cloneEnc(base);
      enc.pool[p] = val;
      const res = await run(enc);
      n++;
      const label = `pool[${p}] = ${val}`;
      if (res.v === 'FAULT') faults.push(`${label}  -> FAULT ${res.reason}`);
      else if (res.v === 'accept') accepts.push(`${label}  -> accept`);
    }
  }

  // --- expression and level table fields -----------------------------------
  // These are covered by _checkTables, but the sweep is only complete if it
  // actually exercises them: an unchecked child index aliases arena nodes the
  // kernel appends later, which is how two earlier holes worked.
  const EXPR_FIELDS = [['a', 0n], ['b', 48n], ['c', 96n]];
  for (let i = 0; i < base.exprTab.length; i++) {
    for (const [nm, shift] of EXPR_FIELDS) {
      const cur = (base.exprTab[i] >> shift) & F;
      for (const val of LADDER(cur)) {
        const enc = cloneEnc(base);
        enc.exprTab[i] = (enc.exprTab[i] & ~(F << shift)) | (val << shift);
        const res = await run(enc);
        n++;
        const label = `expr#${i}.${nm} = ${val}`;
        if (res.v === 'FAULT') faults.push(`${label}  -> FAULT ${res.reason}`);
        else if (res.v === 'accept') accepts.push(`${label}  -> accept`);
      }
    }
  }
  for (let i = 1; i < base.levelTab.length; i++) {
    for (const [nm, shift] of [['a', 0n], ['b', 48n]]) {
      const cur = (base.levelTab[i] >> shift) & F;
      for (const val of LADDER(cur)) {
        const enc = cloneEnc(base);
        enc.levelTab[i] = (enc.levelTab[i] & ~(F << shift)) | (val << shift);
        const res = await run(enc);
        n++;
        const label = `level#${i}.${nm} = ${val}`;
        if (res.v === 'FAULT') faults.push(`${label}  -> FAULT ${res.reason}`);
        else if (res.v === 'accept') accepts.push(`${label}  -> accept`);
      }
    }
  }

  console.log(`field audit: ${file}`);
  console.log(`  mutants run: ${n}`);
  console.log(`  FAULTS  (always a bug): ${faults.length}`);
  for (const f of faults.slice(0, 40)) console.log(`    ${f}`);
  if (faults.length > 40) console.log(`    ... and ${faults.length - 40} more`);
  console.log(`  ACCEPTS (need review): ${accepts.length}`);
  if (!QUIET) for (const a of accepts.slice(0, 60)) console.log(`    ${a}`);
  if (accepts.length > 60) console.log(`    ... and ${accepts.length - 60} more`);

  process.exit(faults.length ? 1 : 0);
}

main().catch((e) => { console.error(e); process.exit(3); });
