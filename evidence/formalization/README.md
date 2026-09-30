# Lean verification records

These compiler and kernel-dependency records correspond to the Lean sources distributed in this repository. Source digests connect the code to the recorded successful compilation.

| Project | Lean | Strict sources | Kernel dependency audit | Source manifest entries |
| --- | --- | --- | --- | --- |
| [`dfl2015`](dfl2015/verification.json) | 4.29.0 | 175 modules, plus the library entry and two audit files | 140 explicit axiom reports | 181 |
| [`sphere433`](sphere433/verification.json) | 4.33.1 | 147 own sources | All 2,108 own declarations | 151 |

## Contents

Each project directory contains:

- `verification.json`: compiler version, dependency revisions, build status, and checked source counts.
- `SHA256SUMS`: source digests with paths relative to the repository root.
- `source_correspondence.json`: checks connecting each distributed source to its compiled digest.
- Build and strict compilation logs, including individual module logs.
- Kernel dependency logs and a structured summary. The permitted dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
- `log_provenance.json`: digests of the verification logs.

The sphere project also records its complete own/native import closure, per-module source digests, compiler versions, and an empty tracked-dependency diff. Its pinned native geometry source closure contains 910 modules.

The main project's two audit sources request axiom reports for 140 selected declarations. The sphere audit covers every own declaration in its imported closure. Compiler builds and strict source checks provide the separate compilation results. The [formalization README](../../formalization/README.md) describes the precise mathematical theorem scope.

## Check source integrity

From the repository root:

```bash
python3 scripts/check_integrity.py
```

The project source manifests can also be checked individually:

```bash
sha256sum -c evidence/formalization/dfl2015/SHA256SUMS
sha256sum -c evidence/formalization/sphere433/SHA256SUMS
```

## Reproduce the Lean checks

Install Git, Python 3, and the Lean toolchains named in the two projects' `lean-toolchain` files. From the repository root, run:

```bash
bash scripts/verify_formalization.sh dfl2015
bash scripts/verify_formalization.sh sphere433
```

The script checks source hashes and toolchain/dependency versions, builds the complete project, strictly compiles each own Lean file, and audits kernel dependencies. Results are written to `verification-results/`. The supplied records in this directory remain available for comparison.

To download the pinned mathlib build cache before compilation, set `DFL_FETCH_CACHE=1`. The number of parallel strict compilation workers can be set with `DFL_VERIFY_WORKERS`; the default is four. A first build may require substantial time and memory.
