# evmlean — a Lean 4 kernel on the EVM

A substantial fragment of the [Lean 4 kernel](https://ammkrn.github.io/type_checking_in_lean4/)
implemented as a Solidity smart contract. It checks declarations in the
[lean4export](https://github.com/leanprover/lean4export) NDJSON format (v3.1.0)
— the same input contract used by the [Lean Kernel Arena](https://arena.lean-lang.org/) —
entirely on the EVM:

- universe levels with the complete `imax` decision procedure;
- expressions, β/δ/ζ/ι reduction, definitional equality with function eta,
  structure/unit eta, and proof irrelevance;
- **inductive families**: strict positivity, constructor validation,
  elimination-universe (large-elim) restrictions, K-flag validation, and
  recursor ι-reduction with K — with recursor declaration tails,
  minor-premise binders, and reduction rules checked against
  **independently reconstructed expected types** (this is what defeats the
  Arena's `nat-rec-rules` attack);
- **multi-type mutual inductive groups**: shared-parameter discipline, block-wide
  positivity and universes, per-type motives/minors ordering, and rule checking
  deferred until every recursor in the block is registered (a rule RHS may call
  a sibling recursor);
- **nested inductives** (`inductive Tree | node : List Tree → Tree`): the export
  erases the auxiliary types but keeps their recursors, so the kernel re-runs
  Lean's nested→mutual elimination internally — discovering each occurrence
  `I Ds`, materialising one auxiliary type per member of `I`'s block, and
  checking positivity on the *expanded* group, which is what makes `List Tree`
  legal and `Cont Bad` illegal. The parametric arguments `Ds` are type-checked
  separately, closing the hole behind [lean4#14576](https://github.com/leanprover/lean4/issues/14576);
- structure projections (typing with the Prop-projection rules + reduction),
  including projection congruence in definitional equality;
- quotients (`Quot.lift`/`Quot.ind` reduction, with canonical primitive
  signature checks);
- Nat literals (typing, literal↔constructor conversion, ι on literals) and the
  full **`reduce_nat`** acceleration — `add sub mul div mod pow gcd beq ble
  land lor xor shiftLeft shiftRight` folded on literal arguments;
- **String literals**, expanded to `String.ofList` of a `Char` list exactly as
  Lean's `string_lit_to_constructor` does, in both ι-reduction and defEq;
- declarations: `axiom`, `def`, `theorem`, `opaque`, `quot`, inductive groups.

Out-of-fragment (honest Arena-style *decline*, exit 2): unsafe/partial
declarations, and Arena exports above the single-transaction checker size guard.
The corpus contains no unsafe/partial declarations at all, and for a *proof*
checker declining them is the conservative reading.

**Headline results** (measured; `gas-report.json`): **143/143 local tests** plus
**zero failures on the full downloadable Arena corpus** (182 exports: 116
good, 66 bad) — 166 exact accept/reject plus 16 honest resource declines, up
from 153 exact + 1 decline + 7 failures (of which five were false rejects on
valid proofs and two were crashes) —
including the Arena's eight adversarial static exports —
each rejected at exactly the poisoned declaration after accepting all legitimate
prelude-style material around it (`Eq.symm`, `false_ne_true`, `Eq.casesOn`,
K-recursors, …). One of those attacks (`level-imax-leq`, which broke nanoda
once) caught a live bug in this kernel during development — fixed and now a
regression test. Kernel size: **61.5KB deployed** — within the EIP-7907
(Glamsterdam) budget this project targets; over today's EIP-170, so on-chain
deployment currently needs a devnet/L2 with a raised limit. 134 of the 143 tests
fit a single post-Fusaka mainnet transaction (≤16.1M gas vs the 16.77M EIP-7825
cap). The seven that do not are the byte-real `lean4export` fixtures (18.0–47.5M):
real Lean declarations pull in `brecOn`, `PProd` and the auxiliary types of
nested inductives, which makes them by far the most expensive things the kernel
checks. They need an L2 or the multi-transaction architecture in PLAN.md §6B.

See **[PLAN.md](PLAN.md)** for the feasibility analysis and roadmap, and
**[HOWTO-ARENA.md](HOWTO-ARENA.md)** for running Lean Kernel Arena tests
against this checker (bundled suite, the Arena's official `lka.py` harness,
or your own `lean4export` output).

## Quickstart

```bash
npm install
npm run gen          # generate the tutorial-parity test vectors
npm test             # compile, install into in-process EVM, run all 143 tests + gas report
npm run size         # report deployed/initcode size against EIP-170/EIP-7907
node scripts/demo-local.js                       # kernel+registry, real submit tx, on-chain record
node bin/evmlean.js tests/arena/nat-rec-rules.ndjson ; echo $?   # Arena checker contract: exit 1 (reject)
```

## Deploy to a real chain

```bash
anvil --code-size-limit 65536        # local chain accepting Glamsterdam-size code
ALLOW_EIP7907=1 RPC_URL=http://127.0.0.1:8545 PRIVATE_KEY=0x... node scripts/deploy.js
KERNEL=0x... node scripts/check-onchain.js tests/good/048_eqRuleK.ndjson
KERNEL=0x... REGISTRY=0x... PRIVATE_KEY=0x... SUBMIT=1 \
  node scripts/check-onchain.js tests/good/048_eqRuleK.ndjson   # permanent record
```

## Layout

```
contracts/LeanKernel.sol       the kernel (stateless check() over a whole export)
contracts/TheoremRegistry.sol  on-chain record of accepted exports (keccak-bound)
tools/lib.js                   NDJSON parser, chain encoder, HOAS test builder
tools/gen_tests.js             generates tests/ (good/bad/decline + manifest)
tools/fetch-arena-tests.sh     re-downloads the Arena's static adversarial tests
tools/run-arena-tests.js       run a downloaded Arena tarball/directory
tools/fuzz.js                  seeded mutation fuzzer (random)
tools/audit-fields.js          exhaustive field-level trust audit (systematic)
tests/nested/ tests/lean/      byte-real fixtures + adversarial soundness regressions
tools/build.js | tools/evm.js  solc artifact cache | in-process EVM harness
test/run.js                    full suite + gas report
bin/evmlean.js                 Arena-style checker entry point ($IN, exit 0/1/2)
scripts/                       deploy.js, check-onchain.js, demo-local.js
arena/evmlean.yaml             checker definition for lean-kernel-arena
tests/arena/                   real Arena adversarial test files
HOWTO-ARENA.md                 how to run Arena tests against this kernel
```

## Design notes

The off-chain encoder is a pure format translation: NDJSON's interned
name/level/expr tables become flat `uint256[]` arrays (one packed word per
node, 48-bit fields); declarations become two-word records; inductive groups
become header+member records with pool-backed metadata (constructor lists,
recursor rules, Nat-literal limbs). Every semantic judgment happens in the
contract. Name identity uses chained keccak content hashes, so the Arena's
renaming-collision attacks are caught on-chain. Recursor *types* are
structurally validated (binder telescope, motive sorts vs the elimination
restriction, K eligibility, level-parameter discipline, indices, major premise,
and final motive application) and recursor *rules* are validated by
reconstructing the expected RHS type from the constructor and recursor
telescopes — imported rules are never compared against themselves.

Verdicts: `0 accept · 1 reject · 2 decline · 3 resource-error`, plus the
failing declaration index and a reason code. Resource exhaustion — the
contract's own step/depth budget, or the host EVM running out of gas or stack —
is reported as a decline, never as a reject and never as a checker fault. That
is the Arena's distinction between "wrong proof", "checker gave up", and
"checker is broken", and only a genuine fault (revert, bad opcode) earns exit 3.

Known limits (documented in PLAN.md): the well-formedness scan is iterative but
type inference and definitional equality still recurse under a depth guard, so
one Arena performance export (a 4000-deep lambda nest) declines on depth rather
than checking. No caching yet, so gas scales with redex count. Research
prototype — not audited.

A red-team audit of this revision produced five distinct exports that an earlier
build accepted as proofs of `False` — a lying constructor-name window, duplicate
entries in that window, `Nat.zero.{u}` read as the literal zero, a forged
`isRec` flag, and an intransitive definitional equality caused by omitting
`reduce_nat` from `whnf`. All are closed, and each is checked in under
`tests/lean/` as a regression that has been verified to fail without its fix.
Every one of them was in a *redundant serialised field* rather than in the type
theory, and none was reachable from any honest exporter — which is why the
Arena corpus stayed green throughout.

`npm run fuzz` runs a seeded mutation fuzzer over the known-good vectors,
asserting the property that matters most for a checker: no input, however
malformed, may produce a *checker error* rather than a verdict.
