# Numerical experiments

This directory contains deterministic computations for the DFL alignment model,
reference data for the manuscript figures, and finite-resolution checks.

## Requirements and quick start

Use Python 3.10 or later with NumPy and Matplotlib. The tested environment
uses Python 3.14.2, NumPy 2.4.3, and Matplotlib 3.10.8. TeX Live with
`pdflatex`, `pgfplots` 1.18, TikZ, and the `standalone` class is needed only
to rebuild the TeX figures. The calculations are deterministic and
self-contained; parameters are fixed in the scripts.

Run the following from the project root:

```sh
python numerics/generate.py
python numerics/phase_dynamics.py
python numerics/transport_atlas.py --skip-tex
python numerics/orientation_sphere.py
python numerics/energy_landscape_3d.py
python numerics/compare_reference.py
```

Each program also accepts `--help` and `--output-dir PATH`. The default output
root is `results/`, regardless of the current working directory. Regenerated
CSVs are written to `results/numerics/data/`, check reports to
`results/numerics/`, and figures to `results/figures/`. The chosen output root
must differ from the project root. Reference files in `numerics/data/` and
`numerics/reference_checks/` are preserved.

Run `phase_dynamics.py` before `energy_landscape_3d.py` to include the latter's
cross-check against the regenerated stationary-state report. By default,
`transport_atlas.py` also compiles its four TeX figure sources.
`scripts/reproduce.py --figures` copies the other figure sources into
`results/figures/` before compiling them.

The recorded five-program run completed in 5.4696 seconds, including both
Matplotlib PDF figures and all default refinement checks. This timing covers
the Python calculations and plotting. TeX compilation has a separate cost.
Execution time depends on hardware and numerical libraries.

## Programs and figure correspondence

| Program | Computation | Associated figures | Check report |
|---|---|---|---|
| `generate.py` | Weighted spectral Galerkin problem, GCI solve, fold root and pressure singularity | `spectrum`, `fold`, `gci_symbol` | `convergence.json` |
| `phase_dynamics.py` | Fixed-mass free-energy envelope and original axisymmetric nonlinear PDE | `phase_landscape`, `quench_dynamics` | `phase_dynamics_check.json` |
| `transport_atlas.py` | First-order SOH wave speeds for three feedback laws, noise boundary, rate threshold and angular fold wedge | `transport_atlas`, `noise_phase_map`, `slow_rate`, `fold_angle_wedge` | `transport_atlas_validation.json` |
| `orientation_sphere.py` | Unit orientation sphere, vMF density and infinitesimal turning response | `orientation_sphere` | `orientation_sphere_check.json` |
| `energy_landscape_3d.py` | Two-dimensional polarization-vector section of the exact fixed-polarization free-energy envelope | `energy_landscape_3d` | `energy_landscape_3d_check.json` |

Figure names in this table omit `.pdf`. `physical_mechanism` is a qualitative
TeX illustration.

## Models, normalization and meaning

Unless stated otherwise, numerical examples use the orientation sphere `S^2`
(ambient dimension `n=3`, intrinsic dimension `d=2`). The manuscript uses
normalized surface measure `d_sigma_2 = dOmega_solid/(4*pi)` and

```text
M_r(t) = exp(r*t)/Z_2(r),  Z_2(r) = sinh(r)/r,
c_2(r) = coth(r) - 1/r,  t = omega dot Omega.
```

The zero-field values are evaluated using their continuous limits. Fold
curves additionally include the ambient dimension `n=5`. Symbols `r`, `rho`,
`J`, polarization `m=J/rho`, energy and SOH speeds use the dimensionless units
of the manuscript. The PDE's time coordinate is named `tau`; noise parameters
are distinct and explicitly stated in the scripts.

### Fixed-field relaxation and GCI comparison

The transverse angular amplitude is approximated in the original weighted
form domain by the Legendre-derivative basis. For `d=2`, the operator is

```text
L_1,r h = -[exp(r*t)*(1-t^2)]^(-1)
          d/dt [exp(r*t)*(1-t^2)^2 * h'] + (2+r*t)*h.
```

The radial partner has potential `2+2*r*t`. The GCI function is obtained by
solving `L_1,r h=1`. The quantity `ctilde` is the weighted average
`integral t*h*p / integral h*p`, with `p=exp(r*t)*(1-t^2)`.

Gauss-Legendre order 240 and Galerkin dimension 24 are compared with order
160 and dimension 16. Exact `S^2` mean and Riccati identities provide
independent normalization and sign checks. The computed eigenvalues and
resolution differences are finite-dimensional numerical evidence. The
full-sphere statements are supplied by the analytic proofs and Lean theorems.

### Feedback, free energy and original PDE

The fold model uses `k(J)=J+J^2`, with `nu(J)=J` and
`D(J)=tau_noise(J)=1/(1+J)`. Its positive equilibria obey
`rho=R_3(r)=j(r)/c_2(r)`, where `j+j^2=r`. At fixed mass and polarization,
the exact free-energy lower envelope is

```text
E_rho(r) = -rho*log Z_2(r) + rho*r*c_2(r) - Phi(rho*c_2(r)),
Phi(J) = J^2/2 + J^3/3.
```

The relative-entropy identity gives this envelope at fixed first moment.
`phase_dynamics.py` starts from vMF initial densities and evolves the full
axisymmetric density through

```text
partial_tau f = partial_t [(1-t^2)*(D(J)*partial_t f - J*f)],
J = (1/2)*integral_{-1}^1 t*f dt.
```

The endpoints have natural zero flux. Scharfetter-Gummel finite-volume
fluxes and implicit Euler with a one-step lag of `J` are used. The reference
runs use 160 cells and `dt=0.04`; the two basin trajectories additionally
compare `(80,0.08)`, `(160,0.04)`, and `(320,0.02)` at `tau=40`. Reports
record mass, positivity, free-energy changes and polarization refinement.

The fold density is about `1.8602147570`, the numerically located equal-energy
density is about `1.9258764318`, and uniform-state loss of local stability
occurs at `rho=3`. These thresholds represent distinct events. The equal-energy
root is reported as a finite-precision calculation. Its global uniqueness
is beyond the numerical evidence provided here. All trajectories evolve
at fixed mass, so their scope is basin selection and fixed-density relaxation.

### Transport and rate figures

`transport_atlas.py` compares linear `k(J)=J`, fold `k(J)=J+J^2`, and
saturated `k(J)=J/[tau0*(epsilon+J)]` feedback. At equal concentration `r`,
these laws have the same angular distribution but different densities.
Transport discriminants describe the first-order SOH principal symbol:
for `K_2=0` this is the full first-order system, and for `K_2>0` it describes
the first-order part. Complex characteristic speeds diagnose the loss of
first-order hyperbolicity. Well-posedness of the kinetic or diffusive
equations requires analysis of their respective operators.

The saturated-feedback zero-pressure curve is sampled and numerically
optimized. Its peak is about `tau0=0.0400289962`. The sampled boundary and
local optimization provide exploratory numerical information; a global
sharp-threshold claim exceeds these checks. The line
`tau0=1/(2*sqrt(5))` is the manuscript's sufficient analytic condition.

The fold wedge compares the directly computed half-angle and imaginary
speed with the analytic `delta^(1/4)` and `delta^(-1/4)` laws. The fold
expansion supplies the exponents and prefactors directly. The rate figure
displays `q_2*lambda_2` as a threshold for guaranteed exponential bounds:
the convergence theorem permits every smaller positive exponent. The exact
nonlinear relaxation exponent requires additional spectral analysis.

### Three-dimensional visualizations

`orientation_sphere.pdf` always displays a unit sphere. Color is probability
per solid angle; the radius specifies the unit orientation geometry. The
signed panel is the exact infinitesimal response
`partial_alpha p_3 = 3*p_3*omega_x` to a rotation of the preferred direction
at fixed concentration. Its parameter is the direction angle. Generator
eigenfunctions and time evolution are studied in the spectral and PDE
experiments, respectively.

`energy_landscape_3d.pdf` displays `m=(m_x,m_y,0)` in polarization-vector
space. Height and color are the exact fixed-polarization energy envelope.
The ring of ordered states is directional degeneracy; in full polarization
space it is a sphere. The surface describes equilibrium energy and barriers
in polarization space. Predictions of transition times or real-space
structures require the corresponding dynamical analysis. The figure uses
DejaVu Sans and English labels on every operating system.

## References and verification

The 20 CSV reference files contain 7,306 data rows. Missing branch segments
are represented by literal `nan` in `phase_branches.csv`; each `nan` marks
a point outside the indicated plotted branch. See [DATA.md](DATA.md) for
file schemas and [PROVENANCE.md](PROVENANCE.md) for methods and validation records.

`compare_reference.py` compares all supplied CSVs and all five canonical
check reports. It permits an absolute difference of `1e-9` plus a relative
difference of `1e-8`, to accommodate library/platform variation. The recorded
run reproduced every checked numeric value exactly. These floating-point
comparisons and refinement checks quantify reproducibility and observed
discretization sensitivity. Their scope stops short of certified
interval-arithmetic or continuum error bounds. Mathematical statements
are proved in the manuscript and formalized in the Lean projects.
