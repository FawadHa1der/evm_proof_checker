# A Lean 4 Kernel on the EVM — Feasibility & Plan

*June 15, 2026 — status: working kernel covering the Arena tutorial fragment exactly; targeting the Glamsterdam (EIP-7907) code-size budget*

## 1. Verdict

Yes — implementing another Lean 4 kernel in Solidity/EVM bytecode is possible, and this repo now implements most of the small-export kernel surface: `contracts/LeanKernel.sol` covers universe algebra with the complete imax decision procedure, β/δ/ζ/ι reduction, definitional equality with function eta, structure/unit eta and proof irrelevance, type inference, and declaration checking for axioms/defs/theorems/opaques, **inductive families** (strict positivity, constructor validation, elimination-universe restrictions, K-flag validation, recursor declaration tails, minor-premise binders, and rules checked against independently reconstructed expected types), **projections** (with the Prop-projection rules), **quotients** (exact canonical primitive signature checks plus `Quot.lift/ind` reduction), and **Nat literals**. It passes 143/143 local tests and has **zero failures on the full downloadable Arena corpus**: 166 exact accept/reject plus 16 resource declines over the full 182-file corpus (116 good, 66 bad). The Arena's eight hand-crafted adversarial static exports are rejected at exactly the poisoned declaration, after accepting the legitimate prelude-style declarations around them (`Eq.symm`, `false_ne_true`, `Eq.casesOn`, K-recursors). 134 of the 143 bundled tests cost ≤16.8M gas — one post-Fusaka mainnet transaction; the seven byte-real lean4export fixtures cost 18.0–47.5M and exceed the EIP-7825 cap.

A satisfying data point on why the Arena matters: its `level-imax-leq` test (which once broke nanoda) caught a live soundness bug in this kernel's first version — the identical-imax shortcut ignored accumulated successor offsets. Independent adversarial test suites work.

The honest qualifications: the kernel is 61.5KB deployed — past today's EIP-170 (24,576 B) limit, deliberately budgeted against [EIP-7907](https://eips.ethereum.org/EIPS/eip-7907)'s 64KB raise proposed for Glamsterdam (until then: devnets/L2s with raised limits, or the M4 library split). The only remaining type-theory decline is unsafe/partial declarations, which is a deliberate reading for a proof checker rather than a gap. Multi-type mutual groups, nested inductives, String-literal constructor reduction and the full `reduce_nat` Nat-literal acceleration are all now implemented. Gas economics still confine single-transaction checking to small exports: `Init.Prelude` is a multi-transaction L2 project (§6 B); mathlib on-chain belongs to the zkVM sidecar with constant ~300k-gas verification (§6 D) — prior art ([zkPi](https://eprint.iacr.org/2024/267), CCS 2024) already proves Lean theorems inside SNARKs.

The Arena explicitly welcomes this kind of entry: *"We welcome more alternative kernel implementations, including incomplete ones, especially if they explore a particular corner of the design space (e.g. … a different host language)"*, and its decline semantics (exit code 2) let a partial checker participate honestly — precedent: the `mini` checker declines 9 tests, `lean4lean` 6.

## 2. What a Lean kernel must do

Per [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/) (Bailey) and [The Type Theory of Lean](https://github.com/digama0/lean-type-theory/releases) (Carneiro), the kernel is a small trusted core that re-checks fully elaborated terms. Its components: names, universe levels (with a complete ≤-decision procedure handling `imax` via case-split on parameters), expressions (8 constructors, de Bruijn indices), an environment of declarations, weak-head normalization (β, δ, ζ, ι, plus quotient and literal reduction), definitional equality (structural + lazy delta + eta + proof irrelevance + unit/structure eta + K-like reduction), type inference, and declaration validation (including the inductive checker: positivity, universe constraints, recursor generation/validation).

The interface to external checkers is the [lean4export](https://github.com/leanprover/lean4export) NDJSON format (v3.1.0): an interned table of names/levels/expressions referenced by integer index, plus declaration records. The Arena runs checkers with `$IN` pointing at such a file; exit 0 = accept, 1 = reject, 2 = decline, anything else = checker bug. Note the format is [still in flux](https://github.com/leanprover/lean4export/issues/3).

Crucially, the export format's interning means the input is already a DAG with explicit sharing — exactly the right shape for an EVM arena-allocator representation (one `uint256` per node here).

## 3. What exists today (this repo)

**Measured results** (in-process EVM, solc 0.8.28, optimizer+viaIR, full table in `gas-report.json`):

| Item | Result |
|---|---|
| Test suite | 143/143: 94 generated + 14 nested + 25 byte-real `lean4export` fixtures (**22 adversarial soundness regressions**) + 10 Arena static tests (8 reject, 2 accept) |
| Full downloadable Arena corpus (182 exports: 116 good, 66 bad) | 166 exact + 16 resource declines; **0 failures** |
| Real Arena adversarial tests | 5/5 rejected at exactly the poisoned declaration |
| Deployed size | LeanKernel 60,897 B (EIP-7954/Glamsterdam 65,536 B budget); TheoremRegistry 1,321 B |
| Trivial decl (`basicDef`) | ~165k gas, 676 B calldata |
| `peano3` (2×2 = 4 via Church numerals) | 2.98M gas |
| Bool/N recursor ι-reduction tests | 0.9–1.5M gas |
| `eqRuleK` (Eq + K-reduction on a stuck major) | 3.38M gas |
| `constlevels` (24 prelude-style decls: Nat, Eq, Eq.symm, false_ne_true, casesOn…) | 6.27M gas |
| Quotients end-to-end (`Quot.lift` ι) | 6.72M gas |
| Registry `submit` (state-writing tx, eqRuleK) | 3.41M gas |

Soundness is exercised adversarially throughout: beyond the original traps (proof irrelevance refused at `Type`, eta refusing unequal bodies, duplicate names/universes, loose bvars…), the suite now covers non-sort inductive types, parameter/level mismatches in constructor results, negative occurrences (incl. behind reducible heads), recursive occurrences in indices, oversized field universes, out-of-range and non-structure projections, wrong recursor rules, malformed recursor result tails, malformed quotient primitive signatures, K on data types, and large elimination from multi-constructor Props — plus the five real Arena attack files.

Pipeline: `tools/lib.js` parses NDJSON and re-encodes it into six flat word arrays (a *pure format translation* — every semantic judgment happens in the contract); `bin/evmlean.js` is an Arena-shaped checker (reads `$IN`, exits 0/1/2 — see HOWTO-ARENA.md); `contracts/TheoremRegistry.sol` records the keccak of accepted exports on-chain; `scripts/deploy.js` + `scripts/check-onchain.js` work against any RPC.

Still declined (honest out-of-fragment verdicts): unsafe/partial declarations, and Arena files above the single-transaction checker guard (`EVMLEAN_MAX_BYTES`, default 128KB). PoC shortcuts that remain (production fixes in §8): no whnf/defEq caching, substitution instead of free-variable contexts, type inference and defEq recurse under a depth guard (~160) instead of an explicit work-stack — the well-formedness scan is already iterative, mostly linear environment scans, always-unfold delta beyond height ordering.

## 4. The EVM constraint map (June 2026)

Why this is hostile territory, with current numbers:

**Per-transaction gas cap — 16,777,216** ([EIP-7825](https://eips.ethereum.org/EIPS/eip-7825), live since Fusaka, Dec 2025). No single L1 transaction can exceed 2²⁴ gas, ever, regardless of what you pay. Consequence: a checker that can't checkpoint its state across transactions caps out around ~16M gas of checking (≈ 5–6 peano3-sized theorems per tx). The multi-tx architecture (§6 B) is therefore *mandatory* for large exports on L1, not an optimization. L2s set their own caps (tens to hundreds of millions; Arbitrum/Base differ), relaxing but not removing this.

**Block gas — 60M** mainnet (raised Nov 2025), EF [targeting 100M+](https://www.blockhead.co/2026/02/20/ethereum-foundation-outlines-2026-protocol-priorities-eyes-100m-gas-limit/) across 2026 forks.

**Code size — 24,576 B** (EIP-170). Current kernel uses 54% of it. A full kernel (inductives + literals + bignum) will not fit in one contract: plan for a facade + `DELEGATECALL` libraries (kernel state lives in memory structs passed internally, so split along feature seams: InductiveChecker, LiteralArith, Reducer). [EIP-7907](https://eips.ethereum.org/EIPS/eip-7907) (raise to 48–64KB, metered) is a Tier-1 candidate for Glamsterdam but not guaranteed — don't bet the architecture on it.

**Calldata pricing.** Post-[EIP-7623](https://eips.ethereum.org/EIPS/eip-7623), data-heavy transactions pay the floor price (10 gas/token ⇒ up to ~40 gas per nonzero byte). Our encoding is word-aligned and zero-rich; measured tutorial calldata is 0.7–4.4KB (negligible vs. execution). But a 3.5MB `Init.Prelude` export ≈ 35–140M gas of *calldata alone* — another forcing function toward L2s, chunked uploads into storage, or commitment-based schemes. Blobs (EIP-4844) don't help directly: the EVM cannot read blob *contents*, only commitments, and the kernel must read every byte it checks.

**No recursion-friendly stack.** 1024-slot operand stack; deep mutual recursion (whnf ↔ inferType ↔ defEq) must eventually become an explicit work-stack in memory. Memory expansion is quadratic past ~720KB per call frame, so the arena strategy (flat `uint256[]`, indices not pointers, in-place growth) matters; at tutorial scale we stay far below the knee.

**No GMP.** Lean's kernel accelerates Nat literals with GMP. The EVM gives native 256-bit arithmetic (+ `MULMOD`, and `MODEXP` precompile) — excellent up to 2²⁵⁶, then limb arithmetic. Strategy: implement Nat literal ops over limbs, decline pathological magnitudes initially.

**What the EVM gives back.** Determinism (perfect for a kernel), metering as a *principled* defense against adversarial exports — the book's [adversarial inputs](https://ammkrn.github.io/type_checking_in_lean4/trust/adversarial_inputs.html) chapter worries about DAG bombs that blow up naive checkers; on the EVM the attacker simply runs out of gas they paid for, and the verdict is "error", never unsoundness. And replayability: acceptance is an EVM trace anyone can re-execute.

## 5. Where this PoC sits vs. the Arena field

The Arena currently benchmarks ~10 checkers (nanoda family in Rust, official C++ kernel, lean4lean in Lean, rpylean in RPython, mini, …) over 102 valid + 49 invalid scored tests, up to a 5.2GB mathlib export; its downloadable tarball excludes the largest valid tests and currently contains 116 good + 66 bad files. evmlean enters as the deliberately exotic corner: ~10⁵–10⁶× slower per declaration than nanoda, but the only one whose verdicts are economically replayable on a public blockchain. Its standing on the Arena's *soundness* axis is already real: all eight reject-expected static tests (`constlevels` even 💥-crashes the official kernel's release build) are correctly rejected at the offending declaration, the two accept-expected ones are accepted, and `level-imax-leq` caught a genuine bug in this kernel during development, the same class of bug it caught in nanoda. Realistic trajectory: pass tutorial/corner-case tests, decline everything large, occupy the bottom of the performance table with pride — the Arena README explicitly frames decline as the honest verdict for out-of-scope tests, and explicitly welcomes incomplete checkers in unusual host languages.

## 6. Architecture options

**A. Single-transaction pure checker (built today).** Stateless `check()` over a whole export. Honest scope: exports up to a few hundred KB and ~16M gas (L1 cap) / more on L2. This is the right vehicle for the Arena tutorial ladder and for "verify this one theorem on-chain" demos.

**B. Multi-transaction checkpointed kernel — the real "Lean kernel as a protocol".** A stateful `Environment` contract: declarations are submitted one (or a batch) per transaction; accepted decls persist (storage: name-hash → record; expression DAG chunks staged via calldata and stored or re-supplied per call with a committed root). Each tx stays under 16.77M gas. The kernel's own structure cooperates — environments grow monotonically, and each decl's check depends only on prior decls. Costs shift to SSTOREs (~20k/slot cold): persisting the prelude's ~10⁴ decl records is millions of gas of storage alone, so store *hashes* of decl payloads and re-supply bodies as calldata on use (verify-against-hash), keeping storage O(1) per decl. This is the purist completion of "another kernel in Solidity," sensibly deployed on an L2 (Base/Arbitrum) where both gas price and tx caps are friendlier.

**C. Optimistic / fraud-proof variant.** Post export + claimed verdict with a bond; challengers bisect the checking trace to a single disputed step executed on-chain (Arbitrum-style). Cheap when unchallenged (O(1) on-chain), but the engineering is dominated by building a deterministic single-step semantics of the checker — that's roughly "build B anyway, plus a dispute game." Worth it only if the goal is a high-throughput public proof market.

**D. zkVM sidecar — the pragmatic endgame for scale.** Run an existing battle-tested checker (nanoda_lib in Rust compiles directly for [SP1](https://docs.succinct.xyz/)/[RISC Zero](https://risczero.com/) RISC-V targets; [lean4lean](https://arxiv.org/abs/2403.14064) via its C backend is also plausible) inside a zkVM; verify the receipt on-chain for a flat ~250–350k gas (Groth16/PLONK verifier), independent of proof size. [zkPi](https://dl.acm.org/doi/10.1145/3658644.3670322) (Laufer–Ozdemir–Boneh, CCS 2024) validated the domain with custom circuits: 57.9% of stdlib / 14.1% of mathlib theorems proven in ≤4.5 min each, with constant-size proofs — the zkVM route trades their per-feature circuit engineering for general-purpose proving overhead and full kernel coverage. Endgame: `TheoremRegistry` accepts *either* direct EVM checking (A/B, small proofs, zero extra trust) *or* a zk receipt (mathlib scale, trust = zkVM circuit + the guest checker binary).

Recommendation: keep A as the Arena artifact and demo; grow it to B on an L2 as the "real" Solidity kernel; add D when scale matters; skip C unless a proof market is the actual product.

## 7. Cost reality (order-of-magnitude; gas prices volatile)

Execution gas measured, prices indicative (L1 base fees have ranged ~0.1–5 gwei in 2026; L2s ~100–1000× cheaper):

| Workload | Gas (est.) | L1 @1 gwei | L2 (typical) |
|---|---|---|---|
| Deploy kernel (today) | 2.7M | ~0.003 ETH | trivial |
| basicDef | 163k | ~$0.5 at $3k/ETH | <$0.01 |
| peano3 (2×2=4), single tx | 2.5M | ~$7 | ~$0.01–0.1 |
| Tutorial suite (43 vectors) | ~25M total | ~$75, 2+ txs | <$1 |
| Init.Prelude (~3.5MB export, arch. B + M2 features) | ~2–20G + calldata | impractical (100s of txs, $10k±) | 10s–100s of $ |
| mathlib (5.2GB export) | ~T-scale | no | no — use D: ~300k gas/batch + off-chain proving |

The per-byte intuition from measurements: ~400–600 gas of checking per export byte on tutorial-shaped content (peano3: 2.52M / 4.4KB). Inductive-heavy real code will be worse; caching (M4) pulls it back down.

## 8. Milestones to a full kernel

Each milestone has Arena tests as its acceptance criterion — the tutorial file is explicitly designed as an implementation ladder.

**M0 — done.** Fragment kernel + tutorial-parity suite + registry + deploy tooling.

**M2/M3 — done (this revision).** Inductive declaration checking (universe/parameter discipline, strict positivity incl. the reduce-before-judging subtleties, constructor result/level validation), recursor validation (telescope structure, motive elimination universes, K-flag eligibility, minor-premise binders and rules checked against **independently reconstructed** expected types — `nat-rec-rules` rejects), ι-reduction with K and Nat-literal majors, structure/unit eta, projections with the Prop rules, exact quotient primitive signature validation + `Quot.lift/ind` ι, Nat literals with limb storage. All five static Arena attack files reject at the right declaration. Cost: kernel grew 13.3KB → 36.7KB (hence the Glamsterdam/EIP-7907 framing).

**M1 — done.** `tools/run-arena-tests.js` ingests the Arena tarball directly. Current acceptance: 133/133 exact on byte-real `tutorial/*`; on the current downloadable tarball, 142 exports are exact accept/reject and the four oversized valid exports decline through the Arena entrypoint size guard. The parser handles sparse name indices and out-of-order level indices. Remaining submission work is administrative: publish a stable repo URL/revision and update `arena/evmlean.yaml`.

**M2.5 — done.** Done: recursor declaration tails validate indices/major/final motive result; recursor names are canonical; constructor-derived recursor minor-premise binders are checked before rule validation; quotient primitive declarations validate exact canonical signatures; official Arena `Acc.rec`, eta/K, quotient, and projection corner tests are covered by the byte-real tutorial sweep. Nested inductives, multi-type mutual groups and String-literal constructor reduction have since been implemented and are covered by byte-real lean4export fixtures.

**M4 — first robustness slice done; optimization remains.** Done: size reporting (`npm run size`), richer `gas-report.json` budget metadata, deploy-time EIP-170/EIP-7907 gates, on-chain EIP-7825 gas warnings, Arena tarball runner, direct environment memo fill on `_envAdd`, smaller well-formedness bitmaps, and large-file Arena declines. Remaining: whnf/defEq caches keyed by node pairs, explicit work-stack replacing recursion, calldata compression, a `DELEGATECALL` library split for today's EIP-170, fuzzing/differential testing, and adversarial gas-bomb tests.

**M5 — stateful multi-tx kernel on an L2 (weeks).** Architecture B: persistent environment, per-decl submission under the tx cap, decl-payload-by-hash storage discipline. Acceptance: all of `Init.Prelude` checked on Base Sepolia for double-digit dollars; a public explorer page of checked decls.

**M6 — zk sidecar (parallel track, weeks).** nanoda_lib (or lean4lean-via-C) in SP1/RISC Zero; on-chain receipt verifier wired into the same registry. Acceptance: one mathlib theorem end-to-end: off-chain proof, ~300k-gas on-chain verification, registry entry indistinguishable in rights from a directly-checked one.

**M7 — hardening & honesty (ongoing).** Property: *no false accepts under any input* — fuzz with mutated exports; bounty the defEq corner cases (eta+K interactions, the `etaRuleK`/`etaCtor` corners from the tutorial, which the official kernel itself treats subtly per [lean4#12520](https://github.com/leanprover/lean4/issues/12520)). Optional flourish: formally verify critical Solidity invariants (Halmos/Certora) — verifying the verifier.

Optional **M8 — gas-golf**: Yul/Huff rewrite of `whnf`/`defEq`/`inst` inner loops (plausible 2–5× on hot paths); EOF if/when it lands.

## 9. Trust: what on-chain checking actually buys

The chain gives *permissionless replayability of the checking computation* and *binding of what was checked*: the registry stores keccak over the entire re-encoded export, so the statement (the `type` field of each theorem) is pinned — anyone can re-derive and pretty-print exactly what was accepted. Three honest caveats, all standard for export-based checkers (the book's trust chapter makes the same points): (1) the encoder is untrusted but can only change *which* export gets checked, never make a bad proof check — and it drops only checking-irrelevant data (binder names, binder-info, mdata), so the binding is up to α-equivalence; (2) meaning lives in the pretty-printer: convincing a human that hash H is "Fermat's Last Theorem" still requires decoding H's statement off-chain; (3) Lean's soundness rests on its theory plus axioms used — the export records axiom dependencies explicitly (this fragment has no built-ins at all: even `aProp` arrives as a declared axiom, and the Arena's `Init.Prelude` pinning policy should be adopted at M5).

On recursors specifically: this kernel never compares imported reduction rules against themselves — each minor-premise binder and rule RHS is checked against an expectation rebuilt from the constructor and recursor telescopes, and the recursor declaration itself must end in `motive indices major`. This is exactly the discipline the Arena's `nat-rec-rules` attack tests for, plus local regressions for malformed eliminator result tails and self-consistent swapped minor premises. Quotient primitives are no longer merely shape-trusted: the checker validates exact canonical binder domains, names, universe arities, and result shapes before enabling quotient reduction.

A pleasant inversion: the EVM's gas model turns the "adversarial input" problem into the submitter's problem. A DAG bomb doesn't hang anyone's CI; it just burns the attacker's ETH and reverts.

## 10. Risks

The export format is explicitly in flux — track lean4export releases; version-gate and decline unknown majors (already implemented). Inductive checking is where soundness bugs live; M2 must be differential-tested against the official kernel before anyone treats registry entries as meaningful. defEq has known dark corners (eta/K interactions) where "what the official kernel does" *is* the spec. EIP landscape may shift sizes/caps (7907, gas-limit raises) — the architecture assumes today's limits and only gets easier. And the obvious one: nobody needs mathlib on L1; the value here is the trust experiment, the Arena diversity entry, and small-proof on-chain verification (proof-gated contracts, bounties paying out on `isChecked(statementHash)` — a "proof market" primitive this registry already supports in miniature).

## 11. Sources

Lean Kernel Arena: https://arena.lean-lang.org/ · [repo/README with checker contract](https://github.com/leanprover/lean-kernel-arena) · [tutorial ladder](https://github.com/leanprover/lean-kernel-arena/blob/master/tutorial/Tutorial.lean)
Format & kernel: [lean4export + NDJSON v3.1.0 spec](https://github.com/leanprover/lean4export) · [format flux issue](https://github.com/leanprover/lean4export/issues/3) · [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/) · [Carneiro, The Type Theory of Lean](https://github.com/digama0/lean-type-theory/releases) · [Lean4Lean paper](https://arxiv.org/abs/2403.14064) · [nanoda_lib](https://github.com/ammkrn/nanoda_lib)
ZK prior art: [zkPi, CCS 2024](https://dl.acm.org/doi/10.1145/3658644.3670322) ([eprint](https://eprint.iacr.org/2024/267))
EVM constraints: [EIP-7825 tx gas cap](https://eips.ethereum.org/EIPS/eip-7825) ([Fusaka activation](https://blog.ethereum.org/2025/10/21/fusaka-gascap-update)) · [60M block gas](https://www.theblock.co/post/380687/ethereum-block-gas-limit-fusaka) · [EF 2026 priorities, 100M target](https://www.blockhead.co/2026/02/20/ethereum-foundation-outlines-2026-protocol-priorities-eyes-100m-gas-limit/) · [EIP-7907 code-size raise](https://eips.ethereum.org/EIPS/eip-7907) · [EIP-7623 calldata floor](https://eips.ethereum.org/EIPS/eip-7623)
defEq corner cases: [lean4#12520](https://github.com/leanprover/lean4/issues/12520)
