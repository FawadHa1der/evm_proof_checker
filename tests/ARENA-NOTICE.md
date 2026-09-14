# Upstream Arena Fixtures

The files in `arena/` and `upstream/` are copied or mechanically exported from
[leanprover/lean-kernel-arena](https://github.com/leanprover/lean-kernel-arena).
The upstream repository's Apache 2.0 license is reproduced in `ARENA-LICENSE`.
The exported fixtures have not been hand-edited or simplified.

`arena/source.json` records the static snapshot revision. `upstream/manifest.json`
records generated-fixture provenance, source links, checksums, outcomes, and
the measured inclusion/exclusion policy. Locally generated exports used the
upstream pinned Lean 4.29.1 toolchain and lean4export 3.1.0. Downloaded tarball
bytes are distinguished from locally generated files in that provenance.

These fixtures are regression evidence, not a specification of Lean's logic.
An upstream `either` outcome permits either accept or reject and is not a
scored soundness or completeness result.
