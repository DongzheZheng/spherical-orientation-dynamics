import DFL.Targets

/-!
# The original spherical marginal: certified elementary cases

All statements below concern `DFL.marginalWeight`, the actual
von Mises--Fisher first-coordinate marginal in `Targets.lean`.  In embedding
dimension three its exponent is zero.  The circle (`n = 2`) has an endpoint
singularity and needs an additional integrability argument; no such result is
asserted merely from this regular case.
-/

namespace DFL

open MeasureTheory
open Filter
open scoped Interval Topology

noncomputable section

private lemma marginalWeight_three (r t : ℝ) :
    marginalWeight 3 r t = Real.exp (r * t) := by
  simp [marginalWeight]

private lemma marginalWeight_three_fun (r : ℝ) :
    marginalWeight 3 r = fun t => Real.exp (r * t) := by
  funext t
  exact marginalWeight_three r t

private lemma marginalWeight_two (r t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    marginalWeight 2 r t = Real.exp (r * t) * (Real.sqrt (1 - t ^ 2))⁻¹ := by
  have hw : 0 ≤ 1 - t ^ 2 := by
    have hprod : 0 ≤ (1 - t) * (1 + t) :=
      mul_nonneg (by linarith [ht.2]) (by linarith [ht.1])
    nlinarith [hprod]
  calc
    marginalWeight 2 r t =
        Real.exp (r * t) * (1 - t ^ 2) ^ ((-1 : ℝ) / 2) := by
          norm_num [marginalWeight]
    _ = Real.exp (r * t) * (Real.sqrt (1 - t ^ 2)) ^ (-1 : ℝ) := by
          rw [Real.rpow_div_two_eq_sqrt (-1) hw]
    _ = Real.exp (r * t) * (Real.sqrt (1 - t ^ 2))⁻¹ := by
          rw [Real.rpow_neg_one]

/-- The integrable square-root endpoint singularity in the circle case is
the original `n = 2` marginal, not an auxiliary smooth substitute. -/
theorem marginalWeight_two_intervalIntegrable (r : ℝ) :
    IntervalIntegrable (marginalWeight 2 r) volume (-1 : ℝ) 1 := by
  have hc : Continuous (fun t : ℝ => Real.exp (r * t)) := by fun_prop
  have hc' : ContinuousOn (fun t : ℝ => Real.exp (r * t))
      (Set.uIcc (-1 : ℝ) 1) := hc.continuousOn
  have hbase : IntervalIntegrable
      (fun t : ℝ => (Real.sqrt (1 - t ^ 2))⁻¹) volume (-1 : ℝ) 1 :=
    by simpa only [Real.sqrt_inv] using
      Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
  have hprod : IntervalIntegrable
      (fun t : ℝ => Real.exp (r * t) * (Real.sqrt (1 - t ^ 2))⁻¹)
      volume (-1 : ℝ) 1 := hbase.continuousOn_mul hc'
  apply hprod.congr
  intro t ht
  have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
    have ht0 : t ∈ Set.Ioc (-1 : ℝ) 1 := by
      simpa only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    exact ⟨ht0.1.le, ht0.2⟩
  exact (marginalWeight_two r t ht').symm

/-- Integrability of the first moment for the original circle marginal. -/
theorem firstMoment_two_intervalIntegrable (r : ℝ) :
    IntervalIntegrable (fun t : ℝ => t * marginalWeight 2 r t)
      volume (-1 : ℝ) 1 := by
  have hc : Continuous (fun t : ℝ => t * Real.exp (r * t)) := by fun_prop
  have hc' : ContinuousOn (fun t : ℝ => t * Real.exp (r * t))
      (Set.uIcc (-1 : ℝ) 1) := hc.continuousOn
  have hbase : IntervalIntegrable
      (fun t : ℝ => (Real.sqrt (1 - t ^ 2))⁻¹) volume (-1 : ℝ) 1 :=
    by simpa only [Real.sqrt_inv] using
      Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
  have hprod : IntervalIntegrable
      (fun t : ℝ => (t * Real.exp (r * t)) * (Real.sqrt (1 - t ^ 2))⁻¹)
      volume (-1 : ℝ) 1 := hbase.continuousOn_mul hc'
  apply hprod.congr
  intro t ht
  have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
    have ht0 : t ∈ Set.Ioc (-1 : ℝ) 1 := by
      simpa only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    exact ⟨ht0.1.le, ht0.2⟩
  change (t * Real.exp (r * t)) * (Real.sqrt (1 - t ^ 2))⁻¹ =
    t * marginalWeight 2 r t
  rw [marginalWeight_two r t ht']
  ring

/-- Positivity of the circle's original partition function.  The integrable
endpoint singularity does not require continuity at the two endpoints. -/
theorem partition_two_pos (r : ℝ) : 0 < partition 2 r := by
  have hpoint : ∀ t : ℝ, t ∈ Set.Ioo (-1 : ℝ) 1 →
      0 < marginalWeight 2 r t := by
    intro t ht
    have hw : 0 < 1 - t ^ 2 := by
      have hprod : 0 < (1 - t) * (1 + t) :=
        mul_pos (by linarith [ht.2]) (by linarith [ht.1])
      nlinarith [hprod]
    rw [marginalWeight_two r t ⟨ht.1.le, ht.2.le⟩]
    exact mul_pos (Real.exp_pos _) (inv_pos.mpr (Real.sqrt_pos.2 hw))
  have hpos : 0 < ∫ t in (-1 : ℝ)..1, marginalWeight 2 r t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (marginalWeight_two_intervalIntegrable r) hpoint
      (by norm_num : (-1 : ℝ) < 1)
  simpa only [partition] using hpos

/-- The original marginal weight is integrable in embedding dimension three. -/
theorem marginalWeight_three_intervalIntegrable (r : ℝ) :
    IntervalIntegrable (marginalWeight 3 r) volume (-1 : ℝ) 1 := by
  have hc : Continuous (fun t : ℝ => Real.exp (r * t)) := by fun_prop
  have hi : IntervalIntegrable (fun t : ℝ => Real.exp (r * t))
      volume (-1 : ℝ) 1 := hc.intervalIntegrable _ _
  rw [marginalWeight_three_fun]
  exact hi

/-- The original first moment is integrable in embedding dimension three. -/
theorem firstMoment_three_intervalIntegrable (r : ℝ) :
    IntervalIntegrable (fun t : ℝ => t * marginalWeight 3 r t)
      volume (-1 : ℝ) 1 := by
  have hc : Continuous (fun t : ℝ => t * Real.exp (r * t)) := by fun_prop
  have hi : IntervalIntegrable (fun t : ℝ => t * Real.exp (r * t))
      volume (-1 : ℝ) 1 := hc.intervalIntegrable _ _
  simpa only [marginalWeight_three_fun] using hi

/-- The original partition function is strictly positive in embedding
dimension three, with no sign restriction on the external field. -/
theorem partition_three_pos (r : ℝ) : 0 < partition 3 r := by
  have hc : Continuous (fun t : ℝ => Real.exp (r * t)) := by fun_prop
  have hc0 : ContinuousOn (fun t : ℝ => Real.exp (r * t))
      (Set.Icc (-1 : ℝ) 1) := hc.continuousOn
  have hc' : ContinuousOn (marginalWeight 3 r) (Set.Icc (-1 : ℝ) 1) := by
    simpa only [marginalWeight_three_fun] using hc0
  have hnonneg : ∀ t ∈ Set.Ioc (-1 : ℝ) 1, 0 ≤ marginalWeight 3 r t := by
    intro t _
    rw [marginalWeight_three]
    positivity
  have hpositive : ∃ t ∈ Set.Icc (-1 : ℝ) 1, 0 < marginalWeight 3 r t := by
    refine ⟨0, by constructor <;> norm_num, ?_⟩
    rw [marginalWeight_three]
    positivity
  have hpos : 0 < ∫ t in (-1 : ℝ)..1, marginalWeight 3 r t :=
    intervalIntegral.integral_pos (by norm_num : (-1 : ℝ) < 1)
      hc' hnonneg hpositive
  simpa only [partition] using hpos

private lemma exponent_nonneg_of_three_le (n : ℕ) (hn : 3 ≤ n) :
    0 ≤ (((n : ℝ) - 3) / 2) := by
  have hnr : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact div_nonneg (sub_nonneg.mpr hnr) (by norm_num)

private lemma coordinate_base_nonneg {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) : 0 ≤ 1 - t ^ 2 := by
  have hprod : 0 ≤ (1 - t) * (1 + t) :=
    mul_nonneg (by linarith [ht.2]) (by linarith [ht.1])
  nlinarith [hprod]

/-- For every embedding dimension at least three, the original spherical
marginal is continuous on its compact integration interval. -/
theorem marginalWeight_continuousOn_of_three_le (n : ℕ) (hn : 3 ≤ n) (r : ℝ) :
    ContinuousOn (marginalWeight n r) (Set.Icc (-1 : ℝ) 1) := by
  have hb : ContinuousOn (fun t : ℝ => 1 - t ^ 2)
      (Set.Icc (-1 : ℝ) 1) := by fun_prop
  have hp : ContinuousOn
      (fun t : ℝ => (1 - t ^ 2) ^ (((n : ℝ) - 3) / 2))
      (Set.Icc (-1 : ℝ) 1) :=
    hb.rpow_const (fun _ _ => Or.inr (exponent_nonneg_of_three_le n hn))
  have he : ContinuousOn (fun t : ℝ => Real.exp (r * t))
      (Set.Icc (-1 : ℝ) 1) := by fun_prop
  simpa only [marginalWeight] using he.mul hp

/-- Integrability of the original spherical marginal in all regular
dimensions `n ≥ 3`. -/
theorem marginalWeight_intervalIntegrable_of_three_le
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) :
    IntervalIntegrable (marginalWeight n r) volume (-1 : ℝ) 1 :=
  (marginalWeight_continuousOn_of_three_le n hn r).intervalIntegrable_of_Icc
    (by norm_num)

/-- Integrability of the original first moment in all `n ≥ 3`. -/
theorem firstMoment_intervalIntegrable_of_three_le
    (n : ℕ) (hn : 3 ≤ n) (r : ℝ) :
    IntervalIntegrable (fun t : ℝ => t * marginalWeight n r t)
      volume (-1 : ℝ) 1 := by
  have hc : ContinuousOn (fun t : ℝ => t * marginalWeight n r t)
      (Set.Icc (-1 : ℝ) 1) :=
    continuousOn_id.mul (marginalWeight_continuousOn_of_three_le n hn r)
  exact hc.intervalIntegrable_of_Icc (by norm_num)

/-- Positivity of the original partition function for all `n ≥ 3`. -/
theorem partition_pos_of_three_le (n : ℕ) (hn : 3 ≤ n) (r : ℝ) :
    0 < partition n r := by
  have hnonneg : ∀ t ∈ Set.Ioc (-1 : ℝ) 1,
      0 ≤ marginalWeight n r t := by
    intro t ht
    have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    simp only [marginalWeight]
    exact mul_nonneg (Real.exp_pos _).le
      (Real.rpow_nonneg (coordinate_base_nonneg ht') _)
  have hpositive : ∃ t ∈ Set.Icc (-1 : ℝ) 1,
      0 < marginalWeight n r t := by
    refine ⟨0, by constructor <;> norm_num, ?_⟩
    simp [marginalWeight]
  have hpos : 0 < ∫ t in (-1 : ℝ)..1, marginalWeight n r t :=
    intervalIntegral.integral_pos (by norm_num : (-1 : ℝ) < 1)
      (marginalWeight_continuousOn_of_three_le n hn r)
      hnonneg hpositive
  simpa only [partition] using hpos

/-- The original weight is integrable in every embedding dimension `n ≥ 2`,
including the circle with its two integrable endpoint singularities. -/
theorem marginalWeight_intervalIntegrable (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    IntervalIntegrable (marginalWeight n r) volume (-1 : ℝ) 1 := by
  rcases eq_or_lt_of_le hn with h | h
  · subst n
    exact marginalWeight_two_intervalIntegrable r
  · exact marginalWeight_intervalIntegrable_of_three_le n (by omega) r

/-- The original first moment is integrable in every `n ≥ 2`. -/
theorem firstMoment_intervalIntegrable (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    IntervalIntegrable (fun t : ℝ => t * marginalWeight n r t)
      volume (-1 : ℝ) 1 := by
  rcases eq_or_lt_of_le hn with h | h
  · subst n
    exact firstMoment_two_intervalIntegrable r
  · exact firstMoment_intervalIntegrable_of_three_le n (by omega) r

/-- Strict positivity of the original partition function for all `n ≥ 2`
and all real external fields. -/
theorem partition_pos (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    0 < partition n r := by
  rcases eq_or_lt_of_le hn with h | h
  · subst n
    exact partition_two_pos r
  · exact partition_pos_of_three_le n (by omega) r

private lemma paired_firstMoment_pos (n : ℕ) {r t : ℝ}
    (hr : 0 < r) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    0 < t * marginalWeight n r t + (-t) * marginalWeight n r (-t) := by
  have hb : 0 < 1 - t ^ 2 := by
    have hprod : 0 < (1 - t) * (1 + t) :=
      mul_pos (by linarith [ht.2]) (by linarith [ht.1])
    nlinarith [hprod]
  have he : Real.exp (r * -t) < Real.exp (r * t) := by
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_pos hr ht.1]
  have hp : 0 < Real.rpow (1 - t ^ 2) (((n : ℝ) - 3) / 2) :=
    Real.rpow_pos_of_pos hb _
  have hid :
      t * marginalWeight n r t + (-t) * marginalWeight n r (-t) =
        t * (Real.exp (r * t) - Real.exp (r * -t)) *
          Real.rpow (1 - t ^ 2) (((n : ℝ) - 3) / 2) := by
    simp only [marginalWeight, neg_sq]
    ring
  rw [hid]
  exact mul_pos (mul_pos ht.1 (sub_pos.mpr he)) hp

/-- The original first moment is positive for every positive field.  The
proof pairs `t` and `-t` in the *same* spherical marginal. -/
theorem firstMoment_pos (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) :
    0 < firstMoment n r := by
  let f : ℝ → ℝ := fun t => t * marginalWeight n r t
  have hfull : IntervalIntegrable f volume (-1 : ℝ) 1 :=
    firstMoment_intervalIntegrable n hn r
  have hleft : IntervalIntegrable f volume (-1 : ℝ) 0 := by
    apply hfull.mono_set'
    intro t ht
    simp only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 0),
      Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht ⊢
    exact ⟨ht.1, le_trans ht.2 (by norm_num)⟩
  have hright : IntervalIntegrable f volume (0 : ℝ) 1 := by
    apply hfull.mono_set'
    intro t ht
    simp only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht ⊢
    exact ⟨lt_trans (by norm_num : (-1 : ℝ) < 0) ht.1, ht.2⟩
  have hflipInt : IntervalIntegrable (fun t => f (-t)) volume (0 : ℝ) 1 := by
    have hf := (IntervalIntegrable.iff_comp_neg
      (a := (-1 : ℝ)) (b := 0) (f := f)).mp hleft
    simpa using hf.symm
  have hpairInt : IntervalIntegrable (fun t => f (-t) + f t)
      volume (0 : ℝ) 1 := hflipInt.add hright
  have hpairPoint : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
      0 < f (-t) + f t := by
    intro t ht
    dsimp [f]
    simpa only [add_comm] using paired_firstMoment_pos n hr ht
  have hpairPos : 0 < ∫ t in (0 : ℝ)..1, f (-t) + f t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hpairInt hpairPoint
      (by norm_num : (0 : ℝ) < 1)
  rw [intervalIntegral.integral_add hflipInt hright] at hpairPos
  have hflip : (∫ t in (0 : ℝ)..1, f (-t)) =
      ∫ t in (-1 : ℝ)..0, f t := by
    simpa only [neg_zero] using (intervalIntegral.integral_comp_neg
      (f := f) (a := (0 : ℝ)) (b := 1))
  rw [hflip] at hpairPos
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  rw [hsplit] at hpairPos
  simpa only [firstMoment] using hpairPos

/-- Positivity of the actual spherical orientation mean in every embedding
dimension `n ≥ 2` and every positive field. -/
theorem orientationMean_pos (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) :
    0 < orientationMean n r := by
  exact div_pos (firstMoment_pos n hn hr) (partition_pos n hn r)

/-- All four integral and sign obligations in `MarginalWellDefined` are
proved for the original marginal.  Differentiability of the quotient remains
a separate analytic obligation. -/
theorem marginal_integrable_and_positive (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) :
    IntervalIntegrable (marginalWeight n r) volume (-1 : ℝ) 1 ∧
    IntervalIntegrable (fun t : ℝ => t * marginalWeight n r t)
      volume (-1 : ℝ) 1 ∧
    0 < partition n r ∧ 0 < orientationMean n r := by
  exact ⟨marginalWeight_intervalIntegrable n hn r,
    firstMoment_intervalIntegrable n hn r,
    partition_pos n hn r,
    orientationMean_pos n hn hr⟩

/-- Pointwise field derivative of the original spherical marginal. -/
theorem marginalWeight_hasDerivAt (n : ℕ) (r t : ℝ) :
    HasDerivAt (fun x : ℝ => marginalWeight n x t)
      (t * marginalWeight n r t) r := by
  unfold marginalWeight
  simpa only [id_eq, one_mul, mul_comm, mul_left_comm, mul_assoc] using
    (((hasDerivAt_id r).mul_const t).exp.mul_const
      (Real.rpow (1 - t ^ 2) (((n : ℝ) - 3) / 2)))

/-- An integrable domination for the parameter derivative on a unit field
neighborhood, including the circle's endpoint singularity. -/
theorem marginalWeight_deriv_bound (n : ℕ) (r x t : ℝ)
    (hx : x ∈ Set.Ioo (r - 1) (r + 1))
    (ht : t ∈ Set.Ioc (-1 : ℝ) 1) :
    ‖t * marginalWeight n x t‖ ≤
      Real.exp (|r| + 1) * marginalWeight n 0 t := by
  have hbase : 0 ≤ Real.rpow (1 - t ^ 2) (((n : ℝ) - 3) / 2) := by
    apply Real.rpow_nonneg
    have hprod : 0 ≤ (1 - t) * (1 + t) :=
      mul_nonneg (by linarith [ht.2]) (by linarith [ht.1])
    nlinarith [hprod]
  have ht_abs : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
  have hx_abs : |x| ≤ |r| + 1 := by
    apply abs_le.mpr
    constructor
    · have h := neg_abs_le r
      linarith [hx.1]
    · have h := le_abs_self r
      linarith [hx.2]
  have hxt : x * t ≤ |r| + 1 := by
    calc
      x * t ≤ |x * t| := le_abs_self _
      _ = |x| * |t| := abs_mul x t
      _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left ht_abs (abs_nonneg x)
      _ = |x| := mul_one _
      _ ≤ |r| + 1 := hx_abs
  have hexp : Real.exp (x * t) ≤ Real.exp (|r| + 1) :=
    Real.exp_le_exp.mpr hxt
  have hscale : |t| * Real.exp (x * t) ≤ Real.exp (|r| + 1) := by
    calc
      |t| * Real.exp (x * t) ≤ 1 * Real.exp (x * t) :=
        mul_le_mul_of_nonneg_right ht_abs (Real.exp_pos _).le
      _ = Real.exp (x * t) := one_mul _
      _ ≤ Real.exp (|r| + 1) := hexp
  calc
    ‖t * marginalWeight n x t‖ =
        (|t| * Real.exp (x * t)) *
          Real.rpow (1 - t ^ 2) (((n : ℝ) - 3) / 2) := by
            simp only [marginalWeight, Real.norm_eq_abs, abs_mul,
              abs_of_pos (Real.exp_pos _), abs_of_nonneg hbase]
            ring
    _ ≤ Real.exp (|r| + 1) *
        Real.rpow (1 - t ^ 2) (((n : ℝ) - 3) / 2) :=
          mul_le_mul_of_nonneg_right hscale hbase
    _ = Real.exp (|r| + 1) * marginalWeight n 0 t := by
          simp [marginalWeight]

/-- Differentiating the original spherical marginal under its integral sign:
the derivative of the partition function is its first moment. -/
theorem partition_hasDerivAt_firstMoment (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    HasDerivAt (partition n) (firstMoment n r) r := by
  let s : Set ℝ := Set.Ioo (r - 1) (r + 1)
  let F : ℝ → ℝ → ℝ := fun x t => marginalWeight n x t
  let F' : ℝ → ℝ → ℝ := fun x t => t * marginalWeight n x t
  let bound : ℝ → ℝ := fun t => Real.exp (|r| + 1) * marginalWeight n 0 t
  have hs : s ∈ 𝓝 r := by
    apply IsOpen.mem_nhds isOpen_Ioo
    dsimp [s]
    constructor <;> dsimp <;> linarith
  have hF_meas : ∀ᶠ x in 𝓝 r,
      AEStronglyMeasurable (F x) (volume.restrict (Ι (-1 : ℝ) 1)) := by
    filter_upwards [] with x
    exact (marginalWeight_intervalIntegrable n hn x).def'.aestronglyMeasurable
  have hF_int : IntervalIntegrable (F r) volume (-1 : ℝ) 1 :=
    marginalWeight_intervalIntegrable n hn r
  have hF'_meas : AEStronglyMeasurable (F' r)
      (volume.restrict (Ι (-1 : ℝ) 1)) :=
    (firstMoment_intervalIntegrable n hn r).def'.aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι (-1 : ℝ) 1 →
      ∀ x ∈ s, ‖F' x t‖ ≤ bound t := by
    filter_upwards [] with t ht x hx
    exact marginalWeight_deriv_bound n r x t hx (by
      simpa only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht)
  have bound_integrable : IntervalIntegrable bound volume (-1 : ℝ) 1 :=
    (marginalWeight_intervalIntegrable n hn 0).const_mul _
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι (-1 : ℝ) 1 →
      ∀ x ∈ s, HasDerivAt (fun x => F x t) (F' x t) x := by
    filter_upwards [] with t ht x hx
    exact marginalWeight_hasDerivAt n x t
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hF_meas hF_int hF'_meas h_bound bound_integrable h_diff
  exact h.2

end

end DFL
