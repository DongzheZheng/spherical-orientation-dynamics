# Reference CSV dictionary

All CSV files use a header, decimal numeric fields, and a comma separator. Values use the dimensionless conventions in [README.md](README.md). `case` is the sole text field.

| File | Rows | Columns |
|---|---:|---|
| `angle.csv` | 181 | `theta_deg`, `discriminant` |
| `fold.csv` | 320 | `r`, `rho3`, `rho5`, `rho3prime` |
| `fold_angle_wedge.csv` | 160 | `delta_rho`, `half_width_deg`, `half_width_asymptotic_deg`, `transverse_imag`, `transverse_imag_asymptotic`, `Theta`, `gamma` |
| `fold_pressure.csv` | 120 | `delta_rho`, `minus_theta`, `fold_asymptotic` |
| `gci_pressure.csv` | 79 | `r`, `ctilde`, `c4`, `c2`, `pressure` |
| `noise_boundary.csv` | 260 | `rho_over_rhoc`, `tau_boundary`, `r` |
| `noise_pressure.csv` | 141 | `rho_over_rhoc`, `tau002`, `tau004`, `tau010`, `tau030` |
| `phase_branches.csv` | 602 | `r`, `rho`, `m`, `saddle_m`, `metastable_m`, `global_m` |
| `phase_landscape.csv` | 450 | `m`, `rho180`, `rhostar`, `rho190`, `rhomaxwell`, `rho200` |
| `quench_critical_large.csv` | 601 | `tau`, `m`, `deltaF` |
| `quench_critical_small.csv` | 601 | `tau`, `m`, `deltaF` |
| `quench_dynamics.csv` | 2004 | `case`, `tau`, `m`, `deltaF` |
| `quench_ordered_basin.csv` | 401 | `tau`, `m`, `deltaF` |
| `quench_profiles.csv` | 160 | `t`, `initial`, `tau2`, `tau10`, `final` |
| `quench_uniform_basin.csv` | 401 | `tau`, `m`, `deltaF` |
| `slow_rate.csv` | 201 | `r`, `rho_minus_3`, `fixed_gap`, `q`, `guaranteed_rate`, `onset_asymptotic` |
| `spectrum.csv` | 81 | `r`, `gap`, `radial`, `splitting` |
| `transport_hysteresis.csv` | 181 | `angle_deg`, `real_plus`, `real_minus`, `imag_abs`, `discriminant` |
| `transport_linear.csv` | 181 | `angle_deg`, `real_plus`, `real_minus`, `imag_abs`, `discriminant` |
| `transport_regularized.csv` | 181 | `angle_deg`, `real_plus`, `real_minus`, `imag_abs`, `discriminant` |

## Field conventions

- `r`: vMF concentration; `rho`: mass/density; `m`: normalized polarization.
- `gap` and `fixed_gap`: transverse fixed-field spectral gap; `radial`: partner eigenvalue; `splitting=radial-gap`.
- `ctilde`, `c_tilde`: GCI weighted mean; `c2`, `c4`: equilibrium polar cosine in the stated intrinsic dimension.
- `rho3`, `rho5`: equilibrium density in ambient dimensions 3 and 5; `rho3prime`: derivative with respect to `r`.
- `delta_rho`: distance from the fold density; `minus_theta` and `Theta`: SOH pressure coefficient with indicated sign.
- `angle_deg`, `theta_deg`: propagation angle in degrees; `real_plus`, `real_minus`, `imag_abs`: characteristic-speed real parts and imaginary magnitude.
- `tau002`, `tau004`, `tau010`, `tau030`: pressure coefficient for saturated-feedback noise values 0.02, 0.04, 0.10 and 0.30.
- `rho_over_rhoc`: density divided by the uniform critical density; `tau_boundary`: numerically sampled zero-pressure noise value.
- `rhostar` and `rhomaxwell` in landscape columns designate curves evaluated at the fold and numerically determined equal-energy densities.
- `saddle_m`, `metastable_m`, `global_m`: disjoint equilibrium branch segments; `nan` marks points outside a segment.
- `tau`: elapsed time in the fixed-mass axisymmetric PDE; `deltaF`: free energy relative to the uniform state.
- `t`: orientation cosine; `initial`, `tau2`, `tau10`, `final`: density profiles at times 0, 2, 10 and 80 for the ordered-basin run.
- `q`: feedback collision-clock factor; `guaranteed_rate=q*fixed_gap` is a bound threshold; `onset_asymptotic=(4/3)*(rho-3)`.
- Columns containing `asymptotic` use exponents and coefficients computed directly from the analytic formulas.

Total reference data rows: 7306.
