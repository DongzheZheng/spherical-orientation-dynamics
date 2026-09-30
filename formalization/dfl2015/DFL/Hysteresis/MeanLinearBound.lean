import DFL.Hysteresis.OriginalRiccati

/-!
An integrating-factor consequence of the original spherical-mean Riccati
identity. It gives a direct comparison with the tangent `r/n` without any
small-field Taylor expansion.
-/

namespace DFL.Hysteresis.MeanLinearBound

open Set

noncomputable def barrier (n : ℕ) (r : ℝ) : ℝ :=
  r ^ (n - 1) * DFL.orientationMean n r - r ^ n / (n : ℝ)

theorem barrier_zero (n : ℕ) (hn : 2 ≤ n) : barrier n 0 = 0 := by
  have hnm1 : n - 1 ≠ 0 := by omega
  have hnpos : n ≠ 0 := by omega
  simp [barrier, hnm1, hnpos]

theorem barrier_deriv_formula (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) :
    deriv (barrier n) r =
      -r ^ (n - 1) * (DFL.orientationMean n r) ^ 2 := by
  let c := DFL.orientationMean n
  have hc : HasDerivAt c (deriv c r) r :=
    (DFL.orientationMean_differentiableAt n hn r).hasDerivAt
  have hp : HasDerivAt (fun x : ℝ => x ^ (n - 1))
      (((n - 1 : ℕ) : ℝ) * r ^ ((n - 1) - 1)) r := by
    simpa using (hasDerivAt_id r).pow (n - 1)
  have hpn : HasDerivAt (fun x : ℝ => x ^ n)
      ((n : ℝ) * r ^ (n - 1)) r := by
    simpa using (hasDerivAt_id r).pow n
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hraw : deriv (barrier n) r =
      (((n - 1 : ℕ) : ℝ) * r ^ ((n - 1) - 1)) * c r +
        r ^ (n - 1) * deriv c r -
        ((n : ℝ) * r ^ (n - 1)) / (n : ℝ) := by
    unfold barrier
    exact ((hp.mul hc).sub (hpn.div_const (n : ℝ))).deriv
  have hkcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have hnat : n - 1 + 1 = n := by omega
    have hreal : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hnat
    linarith
  have hpow : r ^ (n - 1) = r ^ ((n - 1) - 1) * r := by
    calc
      r ^ (n - 1) = r ^ (((n - 1) - 1) + 1) := by congr 1; omega
      _ = r ^ ((n - 1) - 1) * r := pow_succ r _
  dsimp [c] at hraw
  rw [hraw, DFL.orientationMean_riccati n hn hr]
  rw [hpow]
  field_simp
  linear_combination (DFL.orientationMean n r) * hkcast

/-- The original spherical mean lies strictly below its zero-field tangent,
for every positive field, without a Taylor expansion. -/
theorem orientationMean_lt_linear (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) :
    DFL.orientationMean n r < r / (n : ℝ) := by
  have hcont : ContinuousOn (barrier n) (Ici (0 : ℝ)) := by
    intro x _
    have hc : ContinuousAt (DFL.orientationMean n) x :=
      (DFL.orientationMean_differentiableAt n hn x).continuousAt
    have hb : ContinuousAt (barrier n) x := by
      unfold barrier
      exact ((continuousAt_id.pow (n - 1)).mul hc).sub
        ((continuousAt_id.pow n).div_const (n : ℝ))
    exact hb.continuousWithinAt
  have hder : ∀ x ∈ interior (Ici (0 : ℝ)), deriv (barrier n) x < 0 := by
    intro x hx
    have hxpos : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    rw [barrier_deriv_formula n hn hxpos]
    have hcpos : 0 < DFL.orientationMean n x := DFL.orientationMean_pos n hn hxpos
    have hprod : 0 < x ^ (n - 1) * (DFL.orientationMean n x) ^ 2 :=
      mul_pos (pow_pos hxpos _) (sq_pos_of_pos hcpos)
    linarith
  have hanti : StrictAntiOn (barrier n) (Ici (0 : ℝ)) :=
    strictAntiOn_of_deriv_neg (convex_Ici (0 : ℝ)) hcont hder
  have hbarneg : barrier n r < 0 := by
    have h := hanti (by simp : (0 : ℝ) ∈ Ici 0) (by simpa using le_of_lt hr) hr
    simpa [barrier_zero n hn] using h
  have hpow : r ^ n = r ^ (n - 1) * r := by
    calc
      r ^ n = r ^ (n - 1 + 1) := by congr 1; omega
      _ = r ^ (n - 1) * r := pow_succ r _
  have hfac : barrier n r =
      r ^ (n - 1) * (DFL.orientationMean n r - r / (n : ℝ)) := by
    unfold barrier
    rw [hpow]
    ring
  rw [hfac] at hbarneg
  by_contra h
  have hnonneg : 0 ≤ r ^ (n - 1) * (DFL.orientationMean n r - r / (n : ℝ)) :=
    mul_nonneg (le_of_lt (pow_pos hr _)) (by linarith)
  linarith

end DFL.Hysteresis.MeanLinearBound
