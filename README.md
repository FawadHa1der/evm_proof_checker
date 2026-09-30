# evmlean — a Lean 4 kernel on the EVM

A substantial fragment of the [Lean 4 kernel](https://ammkrn.github.io/type_checking_in_lean4/)
implemented as a Solidity smart contract. It checks declarations in the
[lean4export](https://github.com/leanprover/lean4export) NDJSON format (v3.1.0)
— the same input contract used by the [Lean Kernel Arena](https://arena.lean-lang.org/) —
entirely on the EVM:

**DO NOT DEPLOY ON THE BLOCKCHAIN, ONLY MEANT FOR LEAN KERNEL ARENA.**

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

Out-of-fragment (Arena *decline*, exit 2): unsafe/partial declarations,
unsupported inputs, and exhausted size/gas/stack/depth budgets. The current
Arena includes unsafe/partial counterexamples; these still decline intentionally.
The host NDJSON guard defaults to **512,000 bytes**, not an EVM protocol limit.

**September 11, 2026 audit:** the published Arena snapshot lists **208 cases**,
but its tarball contains **187** (114 accept, 73 reject). It excludes 15 unscored
`either` cases and six large library exports. The latest repository adds six
performance cases. We generated the missing small cases with the official
upstream builder and examined a **208-file combined corpus**: the downloaded
187, all 15 `either` cases, and the six new performance cases.

Under the dated **draft Glamsterdam direct-call budget model**, this combined
corpus produces **155 exact verdicts, 8 either-outcome checks, 45 declines,
zero wrong verdicts/faults, and zero size-filter skips**. A decline is not a
passing proof check. Six unavailable large library exports were not executed.
See [the audit report](ARENA-AUDIT-2026-09-11.md) for every excluded case and why.

With a **10-billion local execution allowance**, the same combined corpus
returns **169 exact verdicts, all 15 either cases checked, and 24 declines**,
again with zero wrong verdicts/faults. This is local checking, not single-transaction
eligibility; some small files consume billions of gas.

The default suite now bundles **315 EVM fixtures**: 95 generated, 14 nested,
42 Lean regressions, 15 static Arena files, and **149 newly imported byte-real
Arena exports**, plus separate tooling tests. Imported cases carry checksums,
provenance, explicit outcomes, and transaction-budget regression assertions.
Some older local fixtures deliberately exercise workloads above the L1 budget.

Kernel runtime is **62,472 bytes**, initcode **62,498 bytes**: within the
[EIP-7954](https://eips.ethereum.org/EIPS/eip-7954) targets of 65,536 and 131,072
bytes, respectively, but above EIP-170. Tests use a Cancun EVM with code installed
directly into state. This is **not deployment evidence or a full Glamsterdam
client simulation**. Budget estimates include actual encoded calldata, the
[EIP-7976](https://eips.ethereum.org/EIPS/eip-7976) floor, and the direct-call
intrinsic costs; they do not model registry writes or deployment state gas.

See **[PLAN.md](PLAN.md)** for the feasibility analysis and roadmap, and
**[HOWTO-ARENA.md](HOWTO-ARENA.md)** for running Lean Kernel Arena tests
against this checker (bundled suite, the Arena's official `lka.py` harness,
or your own `lean4export` output).

## Quickstart

```bash
npm install
npm run gen          # generate the tutorial-parity test vectors
npm test             # tooling tests + 315 EVM fixtures + gas report
npm run size         # enforce EIP-7954 code/initcode targets; report EIP-170
node scripts/demo-local.js                       # kernel+registry calls and record in local VM state
node bin/evmlean.js tests/arena/nat-rec-rules.ndjson ; echo $?   # Arena checker contract: exit 1 (reject)
```

## Deploy to a real chain

```bash
anvil --code-size-limit 65536        # raised code limit only; NOT a full fork simulation
ALLOW_EIP7954=1 RPC_URL=http://127.0.0.1:8545 PRIVATE_KEY=0x... node scripts/deploy.js
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
tools/fetch-arena-tests.sh     recursively syncs pinned static Arena tests + YAML outcomes
tools/run-arena-tests.js       run a downloaded Arena tarball/directory
tools/import-arena-tests.js    bundle feasible measured exports with SHA-256 provenance
tools/checker.js               shared checker execution and resource-exit mapping
tools/budgets.js               dated, limited-scope Glamsterdam transaction model
tools/fuzz.js                  seeded mutation fuzzer (random)
tools/audit-fields.js          exhaustive field-level trust audit (systematic)
tests/nested/ tests/lean/      byte-real fixtures + adversarial soundness regressions
tools/build.js | tools/evm.js  solc artifact cache | in-process EVM harness
test/run.js                    full suite + gas report
bin/evmlean.js                 Arena-style checker entry point ($IN, exit 0/1/2)
scripts/                       deploy.js, check-onchain.js, demo-local.js
arena/evmlean.yaml             checker definition for lean-kernel-arena
tests/arena/                   real Arena adversarial test files
tests/upstream/                byte-real upstream fixtures and coverage manifest
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

Known limits (documented in PLAN.md and the dated audit): type inference and
definitional equality still recurse. Some small performance inputs exhaust the
EVM operand stack, while other small exports exceed the execution budget.
Calldata can also exceed its floor budget independently of NDJSON size.
No whnf/defEq caching yet. This remains a research prototype, not a formally
verified kernel or a production security-audited contract.

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
