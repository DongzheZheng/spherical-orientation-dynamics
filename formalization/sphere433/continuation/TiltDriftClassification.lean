import continuation.SphereStrictMonotonicity

/-! The original drift boundary is exact: the positive explicit half-density
exp(rt/2) is the ground at b=0. Actual reflection and strict tilt ordering
then classify the minimum relative to its field-free baseline. -/

noncomputable section
open Set
open scoped RealInnerProductSpace InnerProductSpace
namespace DFLSphere
open DFL.Spectral

/-- At the degenerate drift boundary the genuine full H¹ sphere minimum
is exactly the constant baseline, for every field strength. -/
theorem roundTiltMinimum_drift_zero (k : ℕ) (lam0 r : ℝ) :
    roundTiltMinimum k lam0 r (((k+2 : ℕ) : ℝ)/2) = lam0 := by
  let M : ℕ := k+2
  let a : ℝ := (M : ℝ)/2
  let psi : ℝ → ℝ := halfDensityLift r (fun _ => 1)
  have hM : 2 ≤ M := by dsimp [M]; omega
  have hp : ContDiff ℝ 2 psi := halfDensityLift_smooth r (fun _ => 1) contDiff_const
  have hpos : ∀ t ∈ Icc (-1 : ℝ) 1, 0 < psi t := by
    intro t _
    dsimp [psi, halfDensityLift]
    simpa only [mul_one] using Real.exp_pos ((r/2)*t)
  have heig : ∀ t ∈ Icc (-1 : ℝ) 1, tiltApply M lam0 r a psi t = lam0*psi t := by
    intro t _
    dsimp only [a, psi, tiltApply]
    rw [sub_self, halfDensityApply_lift M 0 lam0 r (fun _ => 1) contDiff_const]
    have hd : deriv (fun _ : ℝ => (1 : ℝ)) = fun _ => 0 := by funext z; exact deriv_const z 1
    simp only [hd, deriv_const, halfDensityLift]
    ring
  obtain ⟨v,hv,_,_⟩ := positive_tilt_eigenprofile_normalized_ground M hM lam0 r a lam0
    psi hp hpos heig
  obtain ⟨u,hu,_⟩ := original_tilt_ground_exists_ge_two M hM lam0 r a
  have he_u := original_tilt_ground_energy M lam0 r a _ u hu
  have he_v := original_tilt_ground_energy M lam0 r a lam0 v hv
  have hlu := hv.rayleigh u hu.smooth
  have hlv := hu.rayleigh v hv.smooth
  rw [hu.normalized, mul_one, he_u] at hlu
  rw [hv.normalized, mul_one, he_v] at hlv
  have hd : M-2 = k := by dsimp [M]; omega
  change roundTiltMinimum k lam0 r a = lam0
  simpa only [hd] using le_antisymm hlv hlu

/-- Every tilt has the same exact baseline at zero field. -/
theorem roundTiltMinimum_zero_field (k : ℕ) (lam0 a : ℝ) :
    roundTiltMinimum k lam0 0 a = lam0 := by
  have hV : roundTiltPotential k lam0 0 a =
      roundTiltPotential k lam0 0 (((k+2 : ℕ) : ℝ)/2) := by
    funext x
    simp only [roundTiltPotential, zero_pow (by decide : 2 ≠ 0), zero_div,
      zero_mul, mul_zero, add_zero, sub_zero]
  change roundPotentialMinimum k (roundTiltPotential k lam0 0 a) = lam0
  rw [hV]
  exact roundTiltMinimum_drift_zero k lam0 0

/-- The degenerate first drift boundary has identically zero actual rate. -/
theorem roundTiltMinimum_deriv_r_drift_zero (k : ℕ) (lam0 r : ℝ) :
    deriv (fun s => roundTiltMinimum k lam0 s (((k+2 : ℕ) : ℝ)/2)) r = 0 := by
  have hf : (fun s => roundTiltMinimum k lam0 s (((k+2 : ℕ) : ℝ)/2)) =
      fun _ => lam0 := funext (roundTiltMinimum_drift_zero k lam0)
  rw [hf, deriv_const]

/-- Reflection gives the second exactly flat drift boundary. -/
theorem roundTiltMinimum_drift_dimension (k : ℕ) (lam0 r : ℝ) :
    roundTiltMinimum k lam0 r (-((k+2 : ℕ) : ℝ)/2) = lam0 := by
  have he : -((k+2 : ℕ) : ℝ)/2 = -(((k+2 : ℕ) : ℝ)/2) := by ring
  rw [he, roundTiltMinimum_even, roundTiltMinimum_drift_zero]

/-- The reflected drift boundary has identically zero actual rate. -/
theorem roundTiltMinimum_deriv_r_drift_dimension (k : ℕ) (lam0 r : ℝ) :
    deriv (fun s => roundTiltMinimum k lam0 s (-((k+2 : ℕ) : ℝ)/2)) r = 0 := by
  have hf : (fun s => roundTiltMinimum k lam0 s (-((k+2 : ℕ) : ℝ)/2)) =
      fun _ => lam0 := funext (roundTiltMinimum_drift_dimension k lam0)
  rw [hf, deriv_const]

/-- A nonzero field raises the true minimum above baseline throughout
0<b<M, with both exact boundary values proved independently. -/
theorem roundTiltMinimum_above_baseline (k : ℕ) (lam0 r b : ℝ)
    (hr : r ≠ 0) (hb : 0 < b) (hbM : b < ((k+2 : ℕ) : ℝ)) :
    lam0 < roundTiltMinimum k lam0 r (((k+2 : ℕ) : ℝ)/2-b) := by
  let a : ℝ := ((k+2 : ℕ) : ℝ)/2-b
  have hM : 0 < ((k+2 : ℕ) : ℝ) := by positivity
  by_cases ha : 0 ≤ a
  · have hab : a < ((k+2 : ℕ) : ℝ)/2 := by dsimp [a]; linarith
    have h := roundTiltMinimum_strictAnti_nonnegative k lam0 r a (((k+2 : ℕ) : ℝ)/2) hr ha hab
    rw [roundTiltMinimum_drift_zero] at h
    exact h
  · have hna : 0 ≤ -a := by linarith
    have hab : -a < ((k+2 : ℕ) : ℝ)/2 := by dsimp [a]; linarith
    have h := roundTiltMinimum_strictAnti_nonnegative k lam0 r (-a) (((k+2 : ℕ) : ℝ)/2) hr hna hab
    rw [roundTiltMinimum_even, roundTiltMinimum_drift_zero] at h
    exact h

/-- Outside the two degenerate drift boundaries a nonzero field lowers
the actual minimum below its baseline. -/
theorem roundTiltMinimum_below_baseline (k : ℕ) (lam0 r b : ℝ)
    (hr : r ≠ 0) (hb : b < 0 ∨ ((k+2 : ℕ) : ℝ) < b) :
    roundTiltMinimum k lam0 r (((k+2 : ℕ) : ℝ)/2-b) < lam0 := by
  have hM : 0 < ((k+2 : ℕ) : ℝ) := by positivity
  rcases hb with hb | hb
  · have h := roundTiltMinimum_strictAnti_nonnegative k lam0 r
      (((k+2 : ℕ) : ℝ)/2) (((k+2 : ℕ) : ℝ)/2-b) hr (by positivity) (by linarith)
    rw [roundTiltMinimum_drift_zero] at h
    exact h
  · have he : ((k+2 : ℕ) : ℝ)/2-b = -(b-((k+2 : ℕ) : ℝ)/2) := by ring
    rw [he, roundTiltMinimum_even]
    have h := roundTiltMinimum_strictAnti_nonnegative k lam0 r
      (((k+2 : ℕ) : ℝ)/2) (b-((k+2 : ℕ) : ℝ)/2) hr (by positivity) (by linarith)
    rw [roundTiltMinimum_drift_zero] at h
    exact h

/-- For nonzero field the two degenerate drift values are exactly the
parameters that preserve the baseline. -/
theorem roundTiltMinimum_eq_baseline_iff (k : ℕ) (lam0 r b : ℝ) (hr : r ≠ 0) :
    roundTiltMinimum k lam0 r (((k+2 : ℕ) : ℝ)/2-b) = lam0 ↔
      b = 0 ∨ b = ((k+2 : ℕ) : ℝ) := by
  constructor
  · intro heq
    by_cases hb0 : b = 0
    · exact Or.inl hb0
    by_cases hbM : b = ((k+2 : ℕ) : ℝ)
    · exact Or.inr hbM
    have habs : False := by
      by_cases hb : b < 0
      · have h := roundTiltMinimum_below_baseline k lam0 r b hr (Or.inl hb)
        rw [heq] at h
        exact lt_irrefl _ h
      by_cases hMb : ((k+2 : ℕ) : ℝ) < b
      · have h := roundTiltMinimum_below_baseline k lam0 r b hr (Or.inr hMb)
        rw [heq] at h
        exact lt_irrefl _ h
      have h := roundTiltMinimum_above_baseline k lam0 r b hr
        (lt_of_le_of_ne (le_of_not_gt hb) (Ne.symm hb0))
        (lt_of_le_of_ne (le_of_not_gt hMb) hbM)
      rw [heq] at h
      exact lt_irrefl _ h
    exact habs.elim
  · rintro (rfl | rfl)
    · simpa only [sub_zero] using roundTiltMinimum_drift_zero k lam0 r
    · have he : ((k+2 : ℕ) : ℝ)/2-((k+2 : ℕ) : ℝ) =
          -((k+2 : ℕ) : ℝ)/2 := by ring
      rw [he]
      exact roundTiltMinimum_drift_dimension k lam0 r

/-- In particular the original physical transverse auxiliary minimum is
strictly above its zero-field baseline at every nonzero field. -/
theorem roundTiltMinimum_physical_above_baseline (k : ℕ) (lam0 r : ℝ) (hr : r ≠ 0) :
    lam0 < roundTiltMinimum k lam0 r ((k : ℝ)/2) := by
  have he : ((k+2 : ℕ) : ℝ)/2-1 = (k : ℝ)/2 := by push_cast; ring
  simpa only [he] using roundTiltMinimum_above_baseline k lam0 r 1 hr (by norm_num)
    (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k])

end DFLSphere
