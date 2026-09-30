import DFL.Geometry.PhysicalSphereTwo
import DFL.Geometry.SuccLawFull
import DFL.Geometry.MomentBridgeSucc
import DFL.Hysteresis.NondegenerateFold

/-!
# DFL single valley on the original physical sphere in every dimension

The proof begins with the cone-induced area measure `volume.toSphere` on
the actual unit sphere. In dimension two its first-coordinate law is the
Chebyshev arcsine measure. In every dimension `k+3≥3`, `SuccLawFull`
proves the full Borel beta law from Euclidean cap volume, including the
equator and poles. Those laws give one common positive normalization for
both moments, hence identify the original physical equilibrium curve with
the paper's one-dimensional marginal curve for every `n≥2`.
-/

namespace DFL.Geometry

noncomputable section

/-- The common-constant moment identity for the original physical sphere
in ambient dimension `k+3`, obtained from its proved Borel coordinate law. -/
theorem sphereMomentBridge_succ (k : ℕ) :
    SphereMomentBridge (k + 3) (by omega) :=
  sphereMomentBridge_succ_of_coordinateLaw k (sphereBetaConst k)
    (sphereBetaConst_pos k) (coordinateLaw_succ_eq_smul_beta k)

/-- The original sphere moments have the paper's marginal law in every
ambient dimension `n≥2`. The singular circle case uses its own exact law. -/
theorem sphereMomentBridge_all (n : ℕ) (hn : 2 ≤ n) :
    SphereMomentBridge n (by omega) := by
  by_cases htwo : n = 2
  · subst n
    exact sphereMomentBridge_two
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k + 3 :=
      ⟨n - 3, by omega⟩
    subst n
    exact sphereMomentBridge_succ k

/-- The 2015 DFL single-valley conjecture on the original physical
`S^(n-1)` with its actual sphere partition function, for every `n≥2`. -/
theorem sphere_isUnimodal_all (n : ℕ) (hn : 2 ≤ n) :
    SphereIsUnimodal n (by omega) :=
  sphere_isUnimodal_of_moment_bridge n hn
    (sphereMomentBridge_all n hn)

/-- The original physical sphere equilibrium-density curve has exactly
one nondegenerate fold in every ambient dimension `n≥2`. -/
theorem sphere_nondegenerateFold_all (n : ℕ) (hn : 2 ≤ n) :
    ∃ rStar : ℝ,
      0 < rStar ∧
      (∀ r : ℝ, 0 < r → r < rStar →
        deriv (sphereEquilibriumDensity n (by omega)) r < 0) ∧
      deriv (sphereEquilibriumDensity n (by omega)) rStar = 0 ∧
      (∀ r : ℝ, rStar < r →
        0 < deriv (sphereEquilibriumDensity n (by omega)) r) ∧
      0 < deriv (deriv (sphereEquilibriumDensity n (by omega))) rStar := by
  have heq := sphereEquilibriumDensity_eq_of_moment_bridge n hn
    (sphereMomentBridge_all n hn)
  simpa only [heq, DFL.NondegenerateFold] using
    (DFL.Hysteresis.original_nondegenerateFold n hn)

end

end DFL.Geometry
