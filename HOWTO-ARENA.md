# Running Lean Kernel Arena tests against evmlean

The [Lean Kernel Arena](https://arena.lean-lang.org/) drives every checker the
same way: it hands the checker a [lean4export NDJSON](https://github.com/leanprover/lean4export/blob/master/format_ndjson.md)
file via the `$IN` environment variable and reads the exit code:
**0 = accept, 1 = reject, 2 = decline (out of scope), anything else = checker bug.**
`bin/evmlean.js` implements exactly this contract, with the actual checking
performed by the `LeanKernel` Solidity contract inside an in-process EVM.

## Route A — the bundled suite (zero setup)

The repo bundles 315 EVM fixtures: 95 generated, 14 nested, 42 Lean regressions,
15 upstream static fixtures, and 149 additional byte-real upstream exports.
`tests/upstream/manifest.json` records checksums, expected outcomes, source
provenance, byte-identical aliases, and budget-based exclusions. Tooling has a
separate unit/integration suite. An Arena `either` outcome permits accept or
reject, but never a decline or fault, and is not a scored soundness result.

```bash
npm install
npm run gen     # regenerate tests/good|bad|decline
npm test        # tooling tests + 315 EVM fixtures, with gas report
```

Run any single export through the Arena-style entry point:

```bash
node bin/evmlean.js tests/arena/nat-rec-rules.ndjson ; echo "exit=$?"   # → 1 (reject)
IN=tests/good/053_quot.ndjson node bin/evmlean.js    ; echo "exit=$?"   # → 0 (accept)
```

To re-download the static Arena files (e.g. after upstream adds new ones, or
because you don't trust the bundled copies):

```bash
bash tools/fetch-arena-tests.sh && npm test
# Or pin an upstream revision / use an existing clone:
node tools/fetch-arena-tests.js --ref=93fdefa10bc7967f475290346005b44de63bfcee
node tools/fetch-arena-tests.js --source=/path/to/lean-kernel-arena
```

## Route B — the Arena's own test set

Most Arena tests (`tutorial/*`, `bogus1`, `proj-of-prop`, `std`, `mathlib`, …)
are *generated* from Lean sources by the Arena's tooling, so they need a Lean
toolchain. Two options:

**B1. Download the test tarball.** The Arena website offers
`lean-arena-tests.tar.gz` for available scored exports no larger than 10 MiB;
on 2026-09-11 it contained 114 good and 73 bad files. It deliberately excludes
all 15 `either` cases and six large library exports. Then run the byte-real
exports through the single-VM harness:

```bash
curl -fsSL https://arena.lean-lang.org/lean-arena-tests.tar.gz -o /tmp/lean-arena-tests.tar.gz
mkdir -p /tmp/lean-arena-tests
tar -xzf /tmp/lean-arena-tests.tar.gz -C /tmp/lean-arena-tests

# Tutorial checks; current unsafe/partial counterexamples intentionally decline.
node tools/run-arena-tests.js /tmp/lean-arena-tests --tutorial --allow-decline

# Submission-shaped check for the downloadable tarball: run every export that
# fits the host NDJSON guard, and count the same explicit size declines
# that bin/evmlean.js will report to the Arena.
node tools/run-arena-tests.js /tmp/lean-arena-tests --entrypoint-max-bytes=512000 --allow-decline --json=corpus-local.json

# Budget-limited direct-call model; still a Cancun VM, NOT a full fork client.
node tools/run-arena-tests.js /tmp/lean-arena-tests --profile=glamsterdam --entrypoint-max-bytes=512000 --allow-decline --json=corpus-glamsterdam.json
```

The local profile defaults to a 10-billion execution-gas allowance. Override it
with `--gas-limit=<integer>` for bounded diagnostics. The `glamsterdam` profile
also constrains execution by the direct-call intrinsic budget and enforces the
calldata floor. `--entrypoint-max-bytes=0` disables the host guard, not those
transaction constraints. `--max-bytes=<n>` *skips* inputs and reports that count;
it is different from an explicit size decline. `--allow-decline` tolerates
declines in the command exit status, but never counts them as exact matches.

**B2. Run the official harness (`lka.py`).** This is how the leaderboard
itself is produced:

```bash
git clone https://github.com/leanprover/lean-kernel-arena && cd lean-kernel-arena
# deps: uv (https://docs.astral.sh/uv/), elan, rustc/cargo, GNU time
#   — or just `nix develop` if you use Nix
uv run lka.py build-test          # builds the test exports (downloads Lean toolchains)
uv run lka.py build-checker       # builds the registered checkers
uv run lka.py run                 # runs checkers × tests
uv run lka.py build-site && python3 -m http.server 8880 --directory _out
```

`build-test`, `build-checker` and `run` accept specific test/checker names to
limit the work (check `uv run lka.py --help`); building *everything* includes
multi-GB mathlib exports you probably don't want locally.

For the cases missing from the tarball, use one pattern per build invocation:

```bash
uv run lka.py build-test 'corner-cases/*'
uv run lka.py build-test nested-nonuniform-param
uv run lka.py build-test 'perf/magma-*'
```

Preserve upstream `outcome:` metadata when assembling generated files under
`good/`, `bad/`, or `either/`. The audit's `assemble-corpus.js` records that
mapping and verifies duplicate bytes. To bundle measured feasible cases:

```bash
node tools/import-arena-tests.js /path/to/combined-corpus combined-glamsterdam.json /path/to/combined-corpus/provenance.json
npm test
```

The importer requires a complete current-build draft-profile report, verifies
SHA-256 hashes, and avoids duplicating byte-identical fixtures already present.

To register evmlean as a checker in your local Arena clone, copy
`arena/evmlean.yaml` into `lean-kernel-arena/checkers/` and edit `url`/`rev`
to point at your published copy of this repo (the Arena builds checkers from
git). The yaml's contract is just:

```yaml
build: npm install --no-audit --no-fund && node tools/build.js
run: node bin/evmlean.js $IN
```

Upstream submission is the same file as a PR to `leanprover/lean-kernel-arena`
(see "Contributing Checkers" in their README; maintainers ask for pinned
revisions and good-faith behavior — checkers are not sandboxed).

## Route C — make your own test from any Lean file

```bash
git clone https://github.com/leanprover/lean4export && cd lean4export
lake build
cd /path/to/your/lean/project
lake env /path/to/lean4export/.lake/build/bin/lean4export YourModule -- yourTheorem > out.ndjson
node /path/to/this/repo/bin/evmlean.js out.ndjson
```

(Keep lean4export's toolchain in sync with your project's `lean-toolchain`;
the export format is versioned and still evolving — evmlean declines major
versions it doesn't recognize.)

## What to expect today

| Test class | Expected result |
|---|---|
| Static Arena fixtures | 10 reject, 3 accept, 2 unscored either outcomes |
| Combined 208-file audit corpus, draft direct-call profile | 155 exact + 8 either checked + 45 declines; 0 wrong verdicts/faults |
| Nested inductives (`numNested > 0`), multi-type mutual blocks, String-literal *reduction*, Nat-literal arithmetic | **checked** — accept/reject on the merits |
| unsafe/partial declarations | decline (exit 2) — a deliberate reading for a proof checker |
| Large perf/init/std/mathlib exports | `bin/evmlean.js` declines files above `EVMLEAN_MAX_BYTES` (default 512000). That's the expected placement for this checker — see PLAN.md §6/§7 for the multi-tx and zkVM routes to scale |

Do not infer transaction feasibility from execution gas or file size alone.
The dated draft model includes actual calldata bytes, intrinsic costs, and
the 64-gas/byte floor. Original large local regression fixtures remain in the
default suite even when they exceed that model. Imported budget-qualified
fixtures must continue to fit or `npm test` fails. See the dated audit and
`gas-report.json` for measurements and limitations.

## On-chain variants

Anything the local runner does can be replayed against a deployed kernel:

```bash
# local node with a raised code-size limit (kernel is 62.5KB — Glamsterdam-class):
anvil --code-size-limit 65536
ALLOW_EIP7954=1 RPC_URL=http://127.0.0.1:8545 PRIVATE_KEY=<anvil key> node scripts/deploy.js
KERNEL=0x... node scripts/check-onchain.js tests/arena/level-imax-leq.ndjson
# record an accepted export permanently:
KERNEL=0x... REGISTRY=0x... PRIVATE_KEY=... SUBMIT=1 node scripts/check-onchain.js tests/good/048_eqRuleK.ndjson
```

Confirm the actual chain's fork and limits before deploying. The current target
is EIP-7954 (65,536-byte runtime; 131,072-byte initcode), not EIP-7907.
The legacy `ALLOW_EIP7907=1` remains an alias, not evidence of fork support.
EIP-8037 separates deployment/registry state gas from execution gas; our pure
direct-call budget model must not be used to estimate those transactions.
No public deployment or publication is performed by the audit commands above.
