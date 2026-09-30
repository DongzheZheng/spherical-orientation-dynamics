# Weighted spherical gap and first eigenspace

This independent Lean 4.33.1 project formalizes the spectral arguments on the genuine unit sphere with its round Riemannian metric, volume, and distributional weak gradient. It supplies the full original-object conclusions of DFL 2013 Conjecture A.1 in the polar-axis coordinates used by the manuscript, together with separate circle and zero-field results.

The canonical `PhysicalSphere k` has sphere dimension `d = k + 1` in ambient dimension `d + 1`. The field is `r` and the canonical polar direction is the first coordinate axis. The generic weak-domain and probability-measure interfaces also accept an arbitrary unit polar direction.

## Main theorem interfaces

| Interface | Conclusion |
| --- | --- |
| `DFLPhysicalGap.actual_physical_gap_eq_transverse` | The complete weighted gap is the original transverse auxiliary minimum, for every `d >= 1` and every real field |
| `DFLOriginalWeakGap.actual_original_weighted_weakH1_gap_sInf` | The same gap is the infimum of the actual Rayleigh quotients on the full original weighted weak H1 domain |
| `DFLOriginalWeakGap.actual_original_weighted_weakH1_rate_iff` | Characterization of every valid Poincare rate on that full weak domain |
| `DFLNormalizedVMF.normalizedSphereVolume_probability` | The genuine normalized vMF measure has total mass one |
| `DFLNormalizedVMF.actual_normalized_weakH1_gap_sInf` and `actual_normalized_weakH1_rate_iff` | The same optimal rate on the normalized vMF probability measure and its actual weak H1 domain |
| `DFLOriginalWeakFirst.original_weighted_weak_equality_common_ground_exists` | For `d >= 2` and `r > 0`, one positive latitude profile classifies all weak first states as `u(x) = inner(a, x) * v(x0)` almost everywhere, with `a` transverse to the polar axis |
| `DFLPhysicalGap.actual_physical_first_smooth_space_finrank` | The actual smooth first eigenspace has dimension `d` for `d >= 2` and `r > 0`; weak first states have the same smooth representatives |
| `DFLPhysicalGap.actual_physical_gap_strictMonoOn` and `actual_physical_gap_deriv_pos` | The actual optimal rate is strictly increasing on nonnegative fields, with strictly positive derivative at positive field |
| `DFLCircleOdd.actual_circle_first_smooth_basis_exists` and `actual_circle_first_smooth_space_finrank` | A complete even/odd smooth first basis with unique coefficients and dimension two, for every real field |

The actual optimal rate is also an even C1 function; its zero-field value is `d`, its derivative at zero is zero, and its nonzero-field value is strictly greater than `d`. Real analyticity is not part of this Lean claim. The package does not claim that numerical strong-field asymptotics or all higher-harmonic decompositions are formalized.

## Source layout

- `DFLSphere433.lean`: library and audit entry.
- `DFLSphere433/`: basic geometry and measure/weak-domain interfaces, plus the original latitude modules ported from the older project.
- `continuation.lean`: completed spectral import entry.
- `continuation/`: original ground state, full-domain variational gap, angular decomposition, Picone equality, first-space recovery, dimension, weak-domain, and vMF normalization modules.
- `DFLSphere433/ContinuationVerification.lean`: kernel dependency audit of every declaration in the own-source import closure.
- `scripts/audit_continuation_closure.py`: source import-closure and forbidden-token audit. This script checks text and hashes; it does not execute Lean.

The proof follows the manuscript: half-density conjugacy; angular mean and deviation; the radial derivative partner; the positive-ground-state Picone identity and cutoff limit; flux Wronskian simplicity; Green moments and Hellmann-Feynman. The original weak-domain bridge uses genuine weak Leibniz rules and smooth density. Ground-state existence, smoothness, simplicity, and full-domain minimization are proved within the imported chain.

## Pinned dependencies

| Component | Version or revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.1` |
| DifferentialGeometry | `7a48598d35109aa99d1cc678e2724c213cdf4ff3` |
| mathlib | `0df444a360eaa60ab8c11dca51a86af692955474` |

The native geometry dependency is fetched from `https://github.com/qinz1yang/differential-geometry`. Its original files are not vendored or modified. All transitive revisions are pinned by `lake-manifest.json`; preserve that lock file when reproducing this release. Dependency attribution is recorded in the release notices.

## Verification

From the package root:

```bash
bash scripts/verify_formalization.sh sphere433
```

The recorded verification used `lake --wfail build DFLSphere433`, then strict per-source compilation with warning-as-error, `autoImplicit=false`, `maxSynthPendingDepth=3`, and the mathlib standard linter set. Only four layout checks were disabled: header, long line, whitespace, and option formatting. The portable runner also verifies dependency revisions, audits the import closure, and records kernel dependencies.

The recorded verification checked all 147 own sources and 2,108 own declarations. The native geometry closure contains 910 sources. Every audited own declaration has only the standard `propext`, `Classical.choice`, and `Quot.sound` dependencies; no missing source or forbidden proof token was found. All 147 Lean source files, three configurations, and the closure audit script retain exactly their compiled bytes.

## Relation to the older project

This project intentionally keeps its own Lean version and dependency graph. A formal equality between its Riemannian volume and the older project's cone-derived spherical measure is not supplied. The independent completed weighted-sphere theorems are therefore stated using their actual Riemannian objects, rather than silently being renamed as cone-measure theorems.
