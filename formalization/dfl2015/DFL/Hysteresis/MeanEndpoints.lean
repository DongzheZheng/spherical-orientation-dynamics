import DFL.Hysteresis.MarginalDerivative

/-!
# Boundary bounds for the original spherical orientation mean

All integrals use the first-coordinate marginal from `DFL.Targets`, including
the integrable singular density in dimension two.  The high-field limit
requires a concentration estimate near `t = 1`; a pointwise bound alone does
not establish that limit.
-/

namespace DFL

open MeasureTheory
open Filter
open scoped Interval Topology

noncomputable section

private lemma marginalWeight_nonneg_on (n : ℕ) (r : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) : 0 ≤ marginalWeight n r t := by
  have hbase : 0 ≤ 1 - t ^ 2 := by
    have hprod : 0 ≤ (1 - t) * (1 + t) :=
      mul_nonneg (by linarith [ht.2]) (by linarith [ht.1])
    nlinarith [hprod]
  exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hbase _)

private lemma marginalWeight_pos_on (n : ℕ) (r : ℝ) {t : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) : 0 < marginalWeight n r t := by
  have hbase : 0 < 1 - t ^ 2 := by
    have hprod : 0 < (1 - t) * (1 + t) :=
      mul_pos (by linarith [ht.2]) (by linarith [ht.1])
    nlinarith [hprod]
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hbase _)

private lemma marginalWeight_exp_mul_base (n : ℕ) (r t : ℝ) :
    marginalWeight n r t = Real.exp (r * t) * marginalWeight n 0 t := by
  simp [marginalWeight]

private lemma baseCap_pos (n : ℕ) (hn : 2 ≤ n) {b : ℝ}
    (hb0 : -1 < b) (hb1 : b < 1) :
    0 < ∫ t in b..(1 : ℝ), marginalWeight n 0 t := by
  have hfull := marginalWeight_intervalIntegrable n hn 0
  have hcap : IntervalIntegrable (marginalWeight n 0)
      volume b (1 : ℝ) := by
    apply hfull.mono_set'
    intro t ht
    simp only [Set.uIoc_of_le hb1.le,
      Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht ⊢
    exact ⟨lt_trans hb0 ht.1, ht.2⟩
  apply intervalIntegral.intervalIntegral_pos_of_pos_on hcap
  · intro t ht
    exact marginalWeight_pos_on n 0 ⟨lt_trans hb0 ht.1, ht.2⟩
  · exact hb1

private lemma gap_intervalIntegrable (n : ℕ) (hn : 2 ≤ n) (r a : ℝ) :
    IntervalIntegrable (fun t : ℝ => (t - a) * marginalWeight n r t)
      volume (-1 : ℝ) 1 := by
  have hfactor : ContinuousOn (fun t : ℝ => t - a)
      (Set.uIcc (-1 : ℝ) 1) := by fun_prop
  simpa only [mul_comm] using
    (marginalWeight_intervalIntegrable n hn r).continuousOn_mul hfactor

private lemma gap_integral_eq (n : ℕ) (hn : 2 ≤ n) (r a : ℝ) :
    (∫ t in (-1 : ℝ)..1, (t - a) * marginalWeight n r t) =
      firstMoment n r - a * partition n r := by
  have hfun : (fun t : ℝ => (t - a) * marginalWeight n r t) =
      (fun t : ℝ => t * marginalWeight n r t - a * marginalWeight n r t) := by
    funext t
    ring
  rw [hfun, intervalIntegral.integral_sub
    (firstMoment_intervalIntegrable n hn r)
    ((marginalWeight_intervalIntegrable n hn r).const_mul a)]
  simp only [intervalIntegral.integral_const_mul, firstMoment, partition]

private lemma restrict_intervalIntegrable {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume (-1 : ℝ) 1)
    {u v : ℝ} (hu : -1 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    IntervalIntegrable f volume u v := by
  apply hf.mono_set'
  intro t ht
  simp only [Set.uIoc_of_le huv,
    Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht ⊢
  exact ⟨lt_of_le_of_lt hu ht.1, le_trans ht.2 hv⟩

private lemma gap_left_lower (n : ℕ) (hn : 2 ≤ n) {r a : ℝ}
    (hr : 0 ≤ r) (ha0 : 0 < a) (ha1 : a < 1) :
    -(2 * Real.exp (r * a)) *
        (∫ t in (-1 : ℝ)..a, marginalWeight n 0 t) ≤
      ∫ t in (-1 : ℝ)..a, (t - a) * marginalWeight n r t := by
  have hbaseInt : IntervalIntegrable (marginalWeight n 0)
      volume (-1 : ℝ) a :=
    restrict_intervalIntegrable (marginalWeight_intervalIntegrable n hn 0)
      (le_refl _) (by linarith) ha1.le
  have hgapInt : IntervalIntegrable
      (fun t : ℝ => (t - a) * marginalWeight n r t)
      volume (-1 : ℝ) a :=
    restrict_intervalIntegrable (gap_intervalIntegrable n hn r a)
      (le_refl _) (by linarith) ha1.le
  have hpoint : ∀ t ∈ Set.Icc (-1 : ℝ) a,
      -(2 * Real.exp (r * a)) * marginalWeight n 0 t ≤
        (t - a) * marginalWeight n r t := by
    intro t ht
    have hbase : 0 ≤ marginalWeight n 0 t :=
      marginalWeight_nonneg_on n 0 ⟨ht.1, le_trans ht.2 ha1.le⟩
    have hta : a - t ≤ 2 := by linarith [ht.1, ha1]
    have hexp : Real.exp (r * t) ≤ Real.exp (r * a) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hr)
    have hcoef : (a - t) * Real.exp (r * t) ≤ 2 * Real.exp (r * a) := by
      calc
        (a - t) * Real.exp (r * t) ≤ 2 * Real.exp (r * t) :=
          mul_le_mul_of_nonneg_right hta (Real.exp_pos _).le
        _ ≤ 2 * Real.exp (r * a) :=
          mul_le_mul_of_nonneg_left hexp (by norm_num)
    have hprod := mul_le_mul_of_nonneg_right hcoef hbase
    rw [marginalWeight_exp_mul_base n r t]
    nlinarith [hprod]
  have hcompare := intervalIntegral.integral_mono_on
    (a := (-1 : ℝ)) (b := a) (by linarith : (-1 : ℝ) ≤ a)
    (hbaseInt.const_mul _) hgapInt hpoint
  simpa only [intervalIntegral.integral_const_mul] using hcompare

private lemma gap_cap_lower (n : ℕ) (hn : 2 ≤ n) {r a b : ℝ}
    (hr : 0 ≤ r) (hab : a < b) (hb1 : b < 1) (ha0 : 0 < a) :
    ((b - a) * Real.exp (r * b)) *
        (∫ t in b..(1 : ℝ), marginalWeight n 0 t) ≤
      ∫ t in b..(1 : ℝ), (t - a) * marginalWeight n r t := by
  have hbaseInt : IntervalIntegrable (marginalWeight n 0)
      volume b (1 : ℝ) :=
    restrict_intervalIntegrable (marginalWeight_intervalIntegrable n hn 0)
      (by linarith) hb1.le (le_refl _)
  have hgapInt : IntervalIntegrable
      (fun t : ℝ => (t - a) * marginalWeight n r t)
      volume b (1 : ℝ) :=
    restrict_intervalIntegrable (gap_intervalIntegrable n hn r a)
      (by linarith) hb1.le (le_refl _)
  have hpoint : ∀ t ∈ Set.Icc b (1 : ℝ),
      ((b - a) * Real.exp (r * b)) * marginalWeight n 0 t ≤
        (t - a) * marginalWeight n r t := by
    intro t ht
    have hbase : 0 ≤ marginalWeight n 0 t :=
      marginalWeight_nonneg_on n 0 ⟨by linarith [hab, ha0, ht.1], ht.2⟩
    have hcoef : (b - a) * Real.exp (r * b) ≤
        (t - a) * Real.exp (r * t) := by
      calc
        (b - a) * Real.exp (r * b) ≤
            (t - a) * Real.exp (r * b) :=
          mul_le_mul_of_nonneg_right (by linarith [ht.1])
            (Real.exp_pos _).le
        _ ≤ (t - a) * Real.exp (r * t) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.1 hr))
            (by linarith [hab, ht.1])
    have hprod := mul_le_mul_of_nonneg_right hcoef hbase
    rw [marginalWeight_exp_mul_base n r t]
    nlinarith [hprod]
  have hcompare := intervalIntegral.integral_mono_on
    (a := b) (b := (1 : ℝ)) hb1.le
    (hbaseInt.const_mul _) hgapInt hpoint
  simpa only [intervalIntegral.integral_const_mul] using hcompare

private lemma gap_integral_lower (n : ℕ) (hn : 2 ≤ n) {r a b : ℝ}
    (hr : 0 ≤ r) (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1) :
    -(2 * Real.exp (r * a)) *
        (∫ t in (-1 : ℝ)..a, marginalWeight n 0 t) +
      ((b - a) * Real.exp (r * b)) *
        (∫ t in b..(1 : ℝ), marginalWeight n 0 t) ≤
      ∫ t in (-1 : ℝ)..1, (t - a) * marginalWeight n r t := by
  have ha1 : a < 1 := lt_trans hab hb1
  have hfull := gap_intervalIntegrable n hn r a
  have hL : IntervalIntegrable
      (fun t : ℝ => (t - a) * marginalWeight n r t)
      volume (-1 : ℝ) a :=
    restrict_intervalIntegrable hfull (le_refl _) (by linarith) ha1.le
  have hM : IntervalIntegrable
      (fun t : ℝ => (t - a) * marginalWeight n r t)
      volume a b :=
    restrict_intervalIntegrable hfull (by linarith) hab.le hb1.le
  have hC : IntervalIntegrable
      (fun t : ℝ => (t - a) * marginalWeight n r t)
      volume b (1 : ℝ) :=
    restrict_intervalIntegrable hfull (by linarith) hb1.le (le_refl _)
  have hLM : IntervalIntegrable
      (fun t : ℝ => (t - a) * marginalWeight n r t)
      volume (-1 : ℝ) b :=
    restrict_intervalIntegrable hfull (le_refl _) (by linarith) hb1.le
  have hmiddle : 0 ≤ ∫ t in a..b,
      (t - a) * marginalWeight n r t := by
    apply intervalIntegral.integral_nonneg hab.le
    intro t ht
    exact mul_nonneg (sub_nonneg.mpr ht.1)
      (marginalWeight_nonneg_on n r
        ⟨by linarith [ha0, ht.1], le_trans ht.2 hb1.le⟩)
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals hL hM
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals hLM hC
  have hleft := gap_left_lower n hn hr ha0 ha1
  have hcap := gap_cap_lower n hn hr hab hb1 ha0
  linarith

/-- The first-coordinate mean never reaches its maximal orientation at any
finite field, because the original marginal has positive interior mass. -/
theorem orientationMean_lt_one (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    orientationMean n r < 1 := by
  have hweight := marginalWeight_intervalIntegrable n hn r
  have hmoment := firstMoment_intervalIntegrable n hn r
  have hfactor : ContinuousOn (fun t : ℝ => 1 - t)
      (Set.uIcc (-1 : ℝ) 1) := by fun_prop
  have hdeficit : IntervalIntegrable
      (fun t : ℝ => (1 - t) * marginalWeight n r t)
      volume (-1 : ℝ) 1 := by
    simpa only [mul_comm] using hweight.continuousOn_mul hfactor
  have hpoint : ∀ t : ℝ, t ∈ Set.Ioo (-1 : ℝ) 1 →
      0 < (1 - t) * marginalWeight n r t := by
    intro t ht
    have hbase : 0 < 1 - t ^ 2 := by
      have hprod : 0 < (1 - t) * (1 + t) :=
        mul_pos (by linarith [ht.2]) (by linarith [ht.1])
      nlinarith [hprod]
    exact mul_pos (by linarith [ht.2])
      (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hbase _))
  have hpos : 0 < ∫ t in (-1 : ℝ)..1,
      (1 - t) * marginalWeight n r t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hdeficit hpoint
      (by norm_num : (-1 : ℝ) < 1)
  have hfun : (fun t : ℝ => (1 - t) * marginalWeight n r t) =
      (fun t : ℝ => marginalWeight n r t - t * marginalWeight n r t) := by
    funext t
    ring
  rw [hfun, intervalIntegral.integral_sub hweight hmoment] at hpos
  have hstrict : firstMoment n r < partition n r := by
    dsimp [firstMoment, partition]
    linarith
  unfold orientationMean
  rw [div_lt_iff₀ (partition_pos n hn r)]
  simpa using hstrict

/-- At every finite positive field the original mean lies strictly between
zero and complete alignment. -/
theorem orientationMean_mem_Ioo_zero_one (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) :
    orientationMean n r ∈ Set.Ioo 0 1 :=
  ⟨orientationMean_pos n hn hr, orientationMean_lt_one n hn r⟩

/-- Exponential tilting eventually raises the original spherical mean above
every fixed threshold strictly below complete alignment.  The proof compares
the positive mass of an interior cap near `t = 1` against the entire lower
orientation interval; it covers the circle's singular endpoints. -/
theorem orientationMean_eventually_gt (n : ℕ) (hn : 2 ≤ n)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ᶠ r : ℝ in atTop, a < orientationMean n r := by
  let b : ℝ := (a + 1) / 2
  have hab : a < b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith
  let L : ℝ := ∫ t in (-1 : ℝ)..a, marginalWeight n 0 t
  let C : ℝ := ∫ t in b..(1 : ℝ), marginalWeight n 0 t
  have hC : 0 < C := baseCap_pos n hn (by linarith [hab, ha0]) hb1
  have hcoef : 0 < (b - a) * C := mul_pos (sub_pos.mpr hab) hC
  have hscale : Tendsto (fun r : ℝ => (b - a) * r) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (sub_pos.mpr hab)).2 tendsto_id
  have hexp : Tendsto (fun r : ℝ => Real.exp ((b - a) * r)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hscale
  have hevent := hexp.eventually_gt_atTop ((2 * L) / ((b - a) * C))
  filter_upwards [hevent, eventually_ge_atTop 0] with r hrExp hr
  have hfactor : Real.exp (r * b) =
      Real.exp (r * a) * Real.exp ((b - a) * r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hraw : 2 * L < Real.exp ((b - a) * r) * ((b - a) * C) :=
    (div_lt_iff₀ hcoef).mp hrExp
  have hraw' := mul_lt_mul_of_pos_right hraw (Real.exp_pos (r * a))
  have hstrict : 2 * Real.exp (r * a) * L <
      ((b - a) * Real.exp (r * b)) * C := by
    calc
      2 * Real.exp (r * a) * L = (2 * L) * Real.exp (r * a) := by ring
      _ < (Real.exp ((b - a) * r) * ((b - a) * C)) *
          Real.exp (r * a) := hraw'
      _ = ((b - a) * Real.exp (r * b)) * C := by rw [hfactor]; ring
  have hbound := gap_integral_lower n hn hr ha0 hab hb1
  have hpositive : 0 < ∫ t in (-1 : ℝ)..1,
      (t - a) * marginalWeight n r t := by
    dsimp [L, C] at hstrict hbound
    linarith
  rw [gap_integral_eq n hn r a] at hpositive
  have hmoment : a * partition n r < firstMoment n r := by linarith
  exact (lt_div_iff₀ (partition_pos n hn r)).mpr hmoment

/-- The original von Mises--Fisher first-coordinate mean converges to full
alignment in the high-field limit, for every embedding dimension `n ≥ 2`.
This includes the singular `n = 2` endpoint density. -/
theorem orientationMean_tendsto_one_atTop (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (orientationMean n) atTop (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    by_cases ha0 : 0 < a
    · exact orientationMean_eventually_gt n hn ha0 ha
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      exact lt_of_le_of_lt (le_of_not_gt ha0) (orientationMean_pos n hn hr)
  · intro a ha
    exact Eventually.of_forall fun r =>
      lt_trans (orientationMean_lt_one n hn r) ha

/-- The original feedback inverse diverges with the applied field. -/
theorem inverseAlignment_tendsto_atTop :
    Tendsto inverseAlignment atTop atTop := by
  have hlin : Tendsto (fun r : ℝ => 1 + 4 * r) atTop atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [eventually_ge_atTop ((B - 1) / 4)] with r hr
    linarith
  have hroot : Tendsto (fun r : ℝ => Real.sqrt (1 + 4 * r))
      atTop atTop := Real.tendsto_sqrt_atTop.comp hlin
  have hshift : Tendsto (fun r : ℝ => Real.sqrt (1 + 4 * r) - 1)
      atTop atTop := by
    simpa only [sub_eq_add_neg] using
      hroot.atTop_add (tendsto_const_nhds (x := (-1 : ℝ)))
  simpa only [inverseAlignment] using
    hshift.atTop_div_const (by norm_num : 0 < (2 : ℝ))

/-- The physical equilibrium-density branch runs to unbounded density at
high field; the orientation mean lies strictly below one at finite field. -/
theorem equilibriumDensity_tendsto_atTop (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (equilibriumDensity n) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [tendsto_atTop.1 inverseAlignment_tendsto_atTop B,
    eventually_gt_atTop (0 : ℝ)] with r hJ hr
  have hc := orientationMean_mem_Ioo_zero_one n hn hr
  have hj : 0 < inverseAlignment r := by
    have harg : 0 ≤ 1 + 4 * r := by linarith
    have hs := Real.sq_sqrt harg
    have hs0 := Real.sqrt_nonneg (1 + 4 * r)
    unfold inverseAlignment
    nlinarith
  have hRge : inverseAlignment r ≤ equilibriumDensity n r := by
    unfold equilibriumDensity
    rw [le_div_iff₀ hc.1]
    nlinarith [mul_lt_mul_of_pos_left hc.2 hj]
  exact le_trans hJ hRge

end

end DFL
