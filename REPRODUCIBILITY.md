# Reproduction guide

## Numerical experiments

The reference tables, reports and plots are in `numerics/data/`, `numerics/reference_checks/` and `figures/reference/`. Regenerated outputs use a separate directory, defaulting to `results/`.

```bash
python scripts/reproduce.py --output-dir results
python scripts/check_numerics.py --output-dir results
```

All six programs use deterministic quadrature, Galerkin discretization, root finding or time stepping. The comparator checks twenty tables and six validation reports against their reference structure, using `atol=1e-9` and `rtol=1e-8`. The original five-program validation run reproduced all numerical entries exactly; its interpreter versions and comparison results are in `evidence/numerics/`. The sixth program supplies independent spatial and temporal refinements of the ordered-basin trajectory.

For an individual experiment:

```bash
python numerics/generate.py --output-dir results
python numerics/phase_dynamics.py --output-dir results
python numerics/transport_atlas.py --output-dir results --skip-tex
python numerics/orientation_sphere.py --output-dir results
python numerics/energy_landscape_3d.py --output-dir results
python numerics/reporting_checks.py --output-dir results
```

Run the first two before the energy landscape, which cross-checks the phase data. `scripts/reproduce.py` uses this order automatically. Script paths can be given in full when working from another directory.

The independent refinement calculation uses `rho=1.90` and initial concentration
`r0=1.80`. It compares `dt=0.08,0.04,0.02` at time 10 with 160 cells, and
80, 160 and 320 cells at time 40 with `dt=0.02`. Its report includes polarization,
relative free energy, mass drift, positivity, free-energy step changes and
successive polarization-difference ratios. These are observed discretization
sensitivities.

## Figures

The numerical suite creates `orientation_sphere.pdf` and `energy_landscape_3d.pdf`. To generate the ten TeX figures from the regenerated tables:

```bash
python scripts/build_figures.py --output-dir results
```

The runner compiles the standalone sources with `pdflatex` and writes final PDFs and editable figure sources to `results/figures/`. It uses temporary compiler files and clears PDF document metadata. All figure sources use English labels and portable fonts.

## Lean proof verification

Install Lean through Elan, together with Git and Python 3. Each project's `lean-toolchain` selects its compiler; `lake-manifest.json` fixes dependency revisions. From the package root:

```bash
bash scripts/verify_formalization.sh dfl2015
bash scripts/verify_formalization.sh sphere433
```

The verifier checks source hashes, compiler versions and dependency revisions, then builds all modules and performs strict source compilation and kernel dependency audits. Results are written to a timestamped directory under `verification-results/`. Optional environment variables are described in `formalization/README.md`.

The supplied compiler and audit records correspond to the source digests in `formalization/source_mapping.json`. Every Lean file and Lake/toolchain configuration matches these digests. Numerical source correspondence and command-line specifications are documented in `numerics/PROVENANCE.md`.

## Integrity

From the package root:

```bash
python scripts/check_integrity.py
```

Alternatively, use a SHA-256 utility:

```bash
shasum -a 256 -c SHA256SUMS
```

On Linux, `sha256sum -c SHA256SUMS` provides the same check. The manifest and checksum list exclude their own files from self-hashing. Regenerated results, dependency caches and virtual environments are excluded from the distributed files.
