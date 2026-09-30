import continuation.PotentialMinimumDependence

/-! Equality in the actual variational lower bound implies stationarity.
The quadratic argument applies to the full H¹ domain, without positivity. -/

noncomputable section
open Bundle Manifold MeasureTheory Set Filter Metric
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DFLSphere
open DifferentialGeometry DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure

section General
variable {H L : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup L] [InnerProductSpace ℝ L]

private def groundDefect (J : H →L[ℝ] L) (P : L →L[ℝ] L) (lam : ℝ) (u v : H) : ℝ :=
  potentialForm J P u v - lam * ⟪J u, J v⟫_ℝ

private theorem groundDefect_perturb (J : H →L[ℝ] L) (P : L →L[ℝ] L)
    (hP : P.IsSymmetric) (lam z : ℝ) (u v : H) :
    groundDefect J P lam (u + z • v) (u + z • v) =
      groundDefect J P lam u u + 2 * z * groundDefect J P lam u v +
        z ^ 2 * groundDefect J P lam v v := by
  have hc : ⟪P (J v), J u⟫_ℝ = ⟪P (J u), J v⟫_ℝ :=
    (hP (J v) (J u)).trans (real_inner_comm _ _)
  simp only [groundDefect, potentialForm, map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm v u, real_inner_comm (J v) (J u), hc]
  ring

private theorem quadratic_linear_zero (b c : ℝ) (hc : 0 ≤ c)
    (h : ∀ z : ℝ, 0 ≤ 2 * z * b + z ^ 2 * c) : b = 0 := by
  have hc1 : 0 < c + 1 := by linarith
  have ht := h (-2 * b / (c + 1))
  have he : 2 * (-2 * b / (c + 1)) * b + (-2 * b / (c + 1)) ^ 2 * c =
      -(4 * b ^ 2) / (c + 1) ^ 2 := by field_simp; ring
  rw [he] at ht
  have hh := (le_div_iff₀ (sq_pos_of_pos hc1)).mp ht
  nlinarith [sq_nonneg b]

/-- A genuine minimum and Rayleigh equality give the polarized weak
operator equation on the same full form domain. -/
theorem potential_form_rayleigh_equality_stationary
    (J : H →L[ℝ] L) (P : L →L[ℝ] L) (hP : P.IsSymmetric) (lam : ℝ)
    (hmin : ∀ w : H, lam * ‖J w‖ ^ 2 ≤ potentialForm J P w w)
    (u : H) (heq : potentialForm J P u u = lam * ‖J u‖ ^ 2) :
    ∀ v : H, potentialForm J P u v = lam * ⟪J u, J v⟫_ℝ := by
  have hnonneg (w : H) : 0 ≤ groundDefect J P lam w w := by
    unfold groundDefect
    rw [real_inner_self_eq_norm_sq]
    exact sub_nonneg.mpr (hmin w)
  have hzero : groundDefect J P lam u u = 0 := by
    unfold groundDefect
    rw [real_inner_self_eq_norm_sq, heq, sub_self]
  intro v
  have hp (z : ℝ) : 0 ≤ 2 * z * groundDefect J P lam u v + z ^ 2 * groundDefect J P lam v v := by
    have h := hnonneg (u + z • v)
    rwa [groundDefect_perturb J P hP, hzero, zero_add] at h
  exact sub_eq_zero.mp (quadratic_linear_zero _ _ (hnonneg v) hp)
end General

end DFLSphere
