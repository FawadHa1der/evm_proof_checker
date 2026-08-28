#!/usr/bin/env node
// Emits the Arena corner-case probes as permanent .ndjson fixtures.
//
// The Lean Kernel Arena ships ~17 hand-written corner-case tests as .lean
// SOURCES only (proj-of-prop, proj-of-imax-prop, proj-of-stuck-prop,
// proj-of-subst-prop, rec-of-subst-prop, proof-irrel, ctor-num-fields,
// k-rec-conv, proj-maybe-prop, ...). Building them needs a Lean toolchain, so
// they never reached this repo's corpus even though they target exactly the
// bug classes from the Aug 2026 kernel soundness bug hunt — including #14807,
// the one nanoda got wrong. These are equivalent exports built directly with
// ExportBuilder, so the behaviours are pinned without a toolchain.
//
//   node tools/gen-arena-probes.js
'use strict';
const fs = require('fs');
const path = require('path');
const { ExportBuilder } = require('./lib');
const V = require('./arena-probe-vectors');

const OUT = path.join(__dirname, '..', 'tests', 'lean');
let n = 0;
for (const [name, [expect, fn]] of Object.entries(V)) {
  const B = new ExportBuilder();
  fn(B);
  const slug = name.replace(/^T\d+[a-z]?_/, '').replace(/([a-z0-9])([A-Z])/g, '$1-$2').toLowerCase();
  const file = `${expect === 'reject' ? 'reject-' : ''}arena-${slug}.ndjson`;
  fs.writeFileSync(path.join(OUT, file), B.emit());
  console.log(`${expect.padEnd(7)} ${file}`);
  n++;
}
console.log(`\nwrote ${n} Arena corner-case fixtures to tests/lean/`);
