# DFL 2015 conjectures

This Lean 4.29.0 project contains the verified sphere-measure, equilibrium-curve, and generalized collision invariant (GCI) arguments used in the manuscript. Its `n` denotes the ambient Euclidean dimension, so the physical sphere is `S^(n-1)` and the manuscript's sphere dimension is `d = n - 1`.

## Main theorem interfaces

| Interface | Conclusion |
| --- | --- |
| `DFL.Geometry.sphere_isUnimodal_all` | The actual spherical equilibrium density curve has a unique single valley, for every ambient dimension `n >= 2` |
| `DFL.Geometry.sphere_nondegenerateFold_all` | Strict derivative signs on the two sides and a positive second derivative at the fold, for every `n >= 2` |
| `DFL.GCI.dfl2015_gci_comparison` | The original angular weak GCI solution exists, is unique with a positive denominator, and satisfies `0 < c_tilde_n < c_n` for all `n >= 2` and positive field |
| `DFL.GCI.original_GCI_all_classicalH10_strict_shift_chain` | The same solution belongs to the genuine classical H1_0 graph closure with the original singular-potential L2 condition, and satisfies `0 < c_tilde_n < c_(n+2) < c_n` |

The geometric marginal identities are derived from the original `volume.toSphere` measure. The root GCI theorem does not assume that a solution, its positivity, or the conjectured coefficient inequality has already been established. Existence uses the original energy form and Lax-Milgram; the comparison uses the original weak tests, endpoint integration by parts, and ground-function comparison.

## Source layout

- `DFL.lean`: main library entry.
- `DFL/Targets.lean`: explicit historical target definitions.
- `DFL/Geometry/`: original spherical measure and coordinate marginal identities.
- `DFL/Hysteresis/`: equilibrium curve, signs, unique valley, and nondegenerate fold.
- `DFL/GCI/`: original weak existence, uniqueness, classical-domain bridge, and strict coefficient comparison.
- `DFL/Spectral/` and `DFL/Probability/`: supporting analytic components. The complete Riemannian sphere spectral result is in the separate `sphere433` project.
- `verification/Audit.lean` and `verification/AuditContinuation.lean`: declaration dependency audits.

All 178 Lean files and three Lake/toolchain configuration files retain their verified source digests.

## Pinned dependencies

| Component | Version or revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.29.0` |
| mathlib | `8a178386ffc0f5fef0b77738bb5449d50efeea95` |

Other transitive dependencies are locked by `lake-manifest.json`. Do not substitute a newer toolchain or update revisions when reproducing this release.

## Verification

From the package root:

```bash
bash scripts/verify_formalization.sh dfl2015
```

The runner selects this project and records the version, build, strict compilations, and declaration audits. The underlying commands include `lake build DFL`, warning-as-error compilation of each own source, and compilation of both audit files.

The recorded build completed successfully and checked all 175 modules individually. The two declaration audits produced 140 axiom reports, all limited to the standard Lean dependencies. The release evidence and source mapping identify exactly which source bytes those results certify.
