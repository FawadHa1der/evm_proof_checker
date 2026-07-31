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
- structure projections (typing with the Prop-projection rules + reduction);
- quotients (`Quot.lift`/`Quot.ind` reduction, with canonical primitive
  signature checks);
- Nat literals (typing, literal↔constructor conversion, ι on literals);
- declarations: `axiom`, `def`, `theorem`, `opaque`, `quot`, inductive groups.

Out-of-fragment (honest Arena-style *decline*, exit 2): nested inductives,
multi-type mutual inductive groups, unsafe/partial declarations, String-literal
reduction, and Arena exports above the single-transaction checker size guard.

**Headline results** (measured; `gas-report.json`): **78/78 local tests** plus
**133/133 exact** on the current byte-real Arena tutorial tarball and **142
exact + 4 explicit size declines** on the current downloadable Arena tarball,
including the Arena's five hand-crafted proof-of-False soundness attacks —
each rejected at exactly the poisoned declaration after accepting all legitimate
prelude-style material around it (`Eq.symm`, `false_ne_true`, `Eq.casesOn`,
K-recursors, …). One of those attacks (`level-imax-leq`, which broke nanoda
once) caught a live bug in this kernel during development — fixed and now a
regression test. Kernel size: **36.8KB deployed** — within the EIP-7907
(Glamsterdam) budget this project targets; over today's EIP-170, so on-chain
deployment currently needs a devnet/L2 with a raised limit. Every test in the
suite fits a single post-Fusaka mainnet transaction (≤6.8M gas vs the 16.77M
cap).

See **[PLAN.md](PLAN.md)** for the feasibility analysis and roadmap, and
**[HOWTO-ARENA.md](HOWTO-ARENA.md)** for running Lean Kernel Arena tests
against this checker (bundled suite, the Arena's official `lka.py` harness,
or your own `lean4export` output).

## Quickstart

```bash
npm install
npm run gen          # generate the tutorial-parity test vectors
npm test             # compile, install into in-process EVM, run all 78 tests + gas report
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
failing declaration index and a reason code. Resource exhaustion is never
reported as reject, matching the Arena's distinction between "wrong proof"
and "checker gave up".

Known limits (documented in PLAN.md): nested inductives, multi-type mutual
inductive groups, and String-literal constructor reduction are deliberately
declined; no caching yet, so gas scales with redex count. Research prototype —
not audited.
