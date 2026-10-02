# Numerical methods and validation records

The six programs compute the reference tables, figures and refinement reports using fixed
quadrature, Galerkin discretization, scalar root finding and time stepping.
Each calculation is deterministic and self-contained. The parameters and
physical interpretation are given in [README.md](README.md); CSV field
names and row counts are listed in [DATA.md](DATA.md).

## Numerical configuration

| Calculation | Reference configuration | Comparison configuration |
|---|---|---|
| Sphere moments, spectrum and GCI | 240 Gauss-Legendre nodes; Galerkin dimension 24 | 160 nodes; dimension 16 |
| Axisymmetric PDE | 160 cells; time step 0.04 | 80 cells/0.08 and 320 cells/0.02 at time 40 |
| Independent temporal refinement | 160 cells; time 10; density 1.90; initial concentration 1.80 | Time steps 0.08, 0.04 and 0.02 |
| Independent spatial refinement | Time step 0.02; time 40; density 1.90; initial concentration 1.80 | 80, 160 and 320 cells |
| Polarization energy surface | 140 radial points; 221 angular points | Scalar inversion residual and stationary-state comparison |
| Orientation density | Unit sphere with concentration 0 or 3 | 96 polar quadrature nodes; 192 equally spaced azimuths |

The spectrum and GCI checks include the exact `S^2` mean and Riccati
identities. The PDE reports record mass error, minimum density, free-energy
changes and polarization refinement. Transport checks compare the speed
formula with direct matrix eigenvalues. The 3D figures include density
normalization, directional-moment and free-energy stationary-state checks.

## Output specification

Each program accepts `--output-dir PATH`. CSV files are written to
`PATH/numerics/data/`, canonical check reports to `PATH/numerics/`, and
figures to `PATH/figures/`. The default is the project's `results/` directory.
The project root is protected as an output destination so the supplied
reference artifacts remain available for comparison.

`transport_atlas.py --skip-tex` computes its tables and report with NumPy.
Figure compilation uses TeX Live and can be requested separately. The two
3D figures use Matplotlib's DejaVu Sans with English labels. File locations
in numerical JSON reports are relative to the output root.

`source_correspondence.json` records source digests, function/class locations
and definition comparisons. The reference artifacts comprise 20 CSV files
and six canonical JSON reports in `reference_checks/`.

`reporting_checks.py` imports the same `run_pde` solver used by the original
trajectory calculation. Its baseline report records the two independent
refinement families, mass conservation, positivity and stepwise free energy.
The successive polarization-difference ratios are 2.0436955 and 4.0053652.

## Recorded comparison

The original five-program run includes the refinements in those programs and
both Matplotlib PDF figures. All 20 regenerated CSV files and every numeric
field in the original five canonical JSON reports agree exactly with the supplied
references in the tested environment:

| Dependency | Tested version |
|---|---|
| Python | 3.14.2 |
| NumPy | 2.4.3 |
| Matplotlib | 3.10.8 |

The recorded execution time is 5.4696 seconds for computation and Matplotlib
plotting. TeX compilation has a separate cost. The run and comparison
records are supplied under `evidence/numerics/`.

`compare_reference.py` checks table structure, text fields, numeric entries
and the six report schemas. Its portable comparison thresholds are
`atol=1e-9` and `rtol=1e-8`. These thresholds allow small library-dependent
floating-point differences. Resolution changes and physical consistency
checks describe observed numerical accuracy; certified continuum error
bounds require additional analysis. The analytic proofs and Lean kernel
checks provide the mathematical theorem evidence.
