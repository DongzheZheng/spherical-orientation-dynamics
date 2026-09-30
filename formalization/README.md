# Lean formalization

Two version-pinned Lean projects implement the equilibrium/GCI results and the Riemannian sphere spectral results. Their dependencies require different Lean versions.

| Project | Lean | Main results | Entry module |
| --- | --- | --- | --- |
| [`dfl2015`](dfl2015/README.md) | 4.29.0 | Single valley, nondegenerate fold, and GCI comparison in the original weak and classical domains | `DFL.lean` |
| [`sphere433`](sphere433/README.md) | 4.33.1 | Full weighted sphere gap, first eigenspace, multiplicity and strict increase of the optimal rate; weak H1 and normalized vMF interfaces | `DFLSphere433.lean` |

## Verification

From the package root, with Elan, Git and Python 3 available:

```bash
bash scripts/verify_formalization.sh dfl2015
bash scripts/verify_formalization.sh sphere433
```

The verifier selects the requested project, checks its source digests and locked dependencies, builds all modules, compiles every source with strict options, and collects kernel dependency reports. `DFL_VERIFY_WORKERS` sets the number of strict-compilation workers, with default 4. `DFL_FETCH_CACHE=1` requests the pinned mathlib build cache. A first build without caches can require substantial time and memory.

All 325 Lean files and their Lake/toolchain configurations match the verified source digests in [`source_mapping.json`](source_mapping.json). Compiler logs, per-source strict compilation records and kernel reports are in [`evidence/formalization`](../evidence/formalization/README.md).

The sphere records cover 147 project sources and 2,108 project declarations, with a transitive geometry source closure of 910 modules. The main records cover 175 modules, the library entry and two declaration audits with 140 reports. The kernel audits allow the standard dependencies `propext`, `Classical.choice` and `Quot.sound`.

## Mathematical scope

The proofs implement the manuscript's weak energy form, endpoint integration by parts, half-density transformation, angular mean decomposition, radial derivative partner, Picone equality, flux Wronskian and Hellmann-Feynman derivative.

The sphere project establishes the optimal rate on the full weighted weak H1 domain, together with the normalization interface for the actual vMF probability measure. First-space classification uses the manuscript's polar-axis coordinates. For sphere dimension `d >= 2` and positive field, the first-space dimension is `d`. On the circle it is two at every real field. At zero field, ambient linear modes give the ordinary round-sphere first eigenspace.

The formal parameter regularity result is C1. Real analyticity and equivalence between the two projects' cone-derived and Riemannian sphere measures remain outside the formal coverage. The numerical experiments provide separate finite-resolution diagnostics and asymptotic comparisons.
