# Physical models and scope

The experiments explore three linked levels of an orientation model. A particle carries a direction on a sphere. Rotational noise spreads directions, while alignment biases them toward the mean polarization. The distinctions below matter when interpreting the figures.

## 1. Frozen-field angular relaxation

For fixed field strength `r`, the stationary orientation density is the von Mises-Fisher distribution, proportional to `exp(r * omega dot Omega)`. The optimal weighted Poincare constant is the slowest nonzero angular relaxation rate. Transverse and radial modes describe different ways to relax: a transverse mode tilts the preferred direction; a radial mode changes concentration about that direction.

The spectral experiment compares these sectors on S2 and tracks their splitting. The Lean sphere project establishes the full weak-domain gap and the complete first eigenspace, with a separate treatment of the circle. Its strict growth result explains why a stronger frozen alignment field accelerates the optimal angular relaxation. Self-consistent branches have feedback-dependent relaxation coefficients, illustrated by the rate experiment.

## 2. Self-consistent polarization and hysteresis

With feedback `k(J) = J + J^2`, the field depends on the polarization magnitude `J`. The equilibrium relation is `J = rho * c(r)` together with `r = k(J)`, where `c(r)` is the stationary mean of `omega dot Omega` for the chosen sphere dimension. A nondegenerate fold creates two ordered branches; a density interval admits both a stable uniform state and a stable ordered state, separated by an unstable branch.

The numerical phase and quench experiments show different basins at the same density and delayed escape from the critical uniform state. The 3D energy surface is a two-component polarization cross-section of the exact fixed-polarization free-energy envelope. Its ring is a consequence of rotational symmetry. Infinite-dimensional basin geometry and kinetic transition times require further dynamical analysis.

## 3. Spatial macroscopic propagation

Generalized collision invariants supply the coefficients of a first-order self-organized hydrodynamics (SOH) closure. The GCI comparison fixes a strict coefficient ordering. The pressure coefficient and the propagation angle then determine whether the characteristic velocities of that first-order principal part are real.

The transport atlas distinguishes the linear feedback model `k(J) = J` from the hysteretic model. It displays oblique propagation, a fold-angle wedge and a noise-pressure map. A complex characteristic velocity diagnoses a failure of hyperbolicity in this first-order principal part. Kinetic stability requires its own analysis. The separately specified diffusion regularization has its own dispersion relation.

## What the package establishes

| Evidence | Scope |
| --- | --- |
| Lean 4.29 project | All-dimension single valley and nondegenerate fold; original weak GCI existence, uniqueness, domain and strict comparison |
| Lean 4.33 project | Actual sphere weak H1 gap, normalized vMF interface, first-mode classification, multiplicity, evenness, C1 regularity and strict growth |
| Numerical core | S2 spectral sector comparison, n=3 and n=5 folds, GCI coefficients and first-order transport diagnostics |
| Phase dynamics | Finite-resolution homogeneous evolution and basin examples |
| 3D and qualitative plots | Orientation geometry, fixed-polarization energy landscape and relations among the physical descriptions |

The formalized sphere regularity is C1. Real analyticity and identification of the two sphere-measure constructions remain outside the formal coverage. The numerical convergence reports compare resolutions and analytic identities using floating-point arithmetic; certified interval error bounds lie outside the supplied numerical evidence. These distinctions are retained throughout the documentation.
