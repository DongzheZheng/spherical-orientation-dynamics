import DFL.Hysteresis.MeanSmallField
import DFL.Hysteresis.OriginalRiccati

/-!
# Strict ordering of the original DFL orientation means across dimensions

The first-coordinate laws in embedding dimensions `n` and `n + 2` are
compared through their independently proved Riccati equations and their
zero-field susceptibilities. No ordering of the measures is assumed.
-/

namespace DFL.Hysteresis.DimensionShift

open Set Filter MeasureTheory
open scoped Topology Interval

noncomputable section

private def gap (n : ℕ) (r : ℝ) : ℝ :=
  DFL.orientationMean n r - DFL.orientationMean (n + 2) r

private def coefficient (n : ℕ) (r : ℝ) : ℝ :=
  ((n : ℝ) - 1) / r + DFL.orientationMean n r +
    DFL.orientationMean (n + 2) r

private def source (n : ℕ) (r : ℝ) : ℝ :=
  2 * DFL.orientationMean (n + 2) r / r

private theorem gap_hasDerivAt (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (gap n) (source n r - coefficient n r * gap n r) r := by
  have hn2 : 2 ≤ n + 2 := by omega
  have hcn := (DFL.orientationMean_differentiableAt n hn r).hasDerivAt
  have hcn2 := (DFL.orientationMean_differentiableAt (n + 2) hn2 r).hasDerivAt
  have hraw := hcn.sub hcn2
  convert hraw using 1
  rw [DFL.orientationMean_riccati n hn hr,
    DFL.orientationMean_riccati (n + 2) hn2 hr]
  dsimp [gap, coefficient, source]
  have hrne : r ≠ 0 := ne_of_gt hr
  field_simp
  push_cast
  ring

private theorem source_pos (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) :
    0 < source n r := by
  have hn2 : 2 ≤ n + 2 := by omega
  exact div_pos (mul_pos (by norm_num) (DFL.orientationMean_pos (n + 2) hn2 hr)) hr

private theorem coefficient_continuousOn (n : ℕ) (hn : 2 ≤ n) :
    ContinuousOn (coefficient n) (Ioi (0 : ℝ)) := by
  intro r hr
  have hrne : r ≠ 0 := ne_of_gt hr
  have hc : ContinuousAt (DFL.orientationMean n) r :=
    (DFL.orientationMean_differentiableAt n hn r).continuousAt
  have hn2 : 2 ≤ n + 2 := by omega
  have hc2 : ContinuousAt (DFL.orientationMean (n + 2)) r :=
    (DFL.orientationMean_differentiableAt (n + 2) hn2 r).continuousAt
  unfold coefficient
  fun_prop (discharger := assumption)

private theorem coefficient_intervalIntegrable (n : ℕ) (hn : 2 ≤ n)
    {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) :
    IntervalIntegrable (coefficient n) volume δ r := by
  have hsubset : Set.uIcc δ r ⊆ Ioi (0 : ℝ) := by
    intro x hx
    rcases le_total δ r with hle | hle
    · rw [uIcc_of_le hle] at hx
      exact lt_of_lt_of_le hδ hx.1
    · rw [uIcc_of_ge hle] at hx
      exact lt_of_lt_of_le hr hx.1
  exact ((coefficient_continuousOn n hn).mono hsubset).intervalIntegrable

private def factor (n : ℕ) (δ r : ℝ) : ℝ :=
  Real.exp (∫ u in δ..r, coefficient n u)

private def K (n : ℕ) (δ r : ℝ) : ℝ := factor n δ r * gap n r

private theorem factor_pos (n : ℕ) (δ r : ℝ) : 0 < factor n δ r := by
  unfold factor
  exact Real.exp_pos _

private theorem K_hasDerivAt (n : ℕ) (hn : 2 ≤ n)
    {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) :
    HasDerivAt (K n δ) (factor n δ r * source n r) r := by
  have hcont : ContinuousAt (coefficient n) r :=
    (coefficient_continuousOn n hn).continuousAt (IsOpen.mem_nhds isOpen_Ioi hr)
  have hint := coefficient_intervalIntegrable n hn hδ hr
  have hmeas : StronglyMeasurableAtFilter (coefficient n) (𝓝 r) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
      (coefficient_continuousOn n hn) r hr
  have hI : HasDerivAt (fun x : ℝ => ∫ u in δ..x, coefficient n u)
      (coefficient n r) r :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  have hfactor : HasDerivAt (factor n δ)
      (coefficient n r * factor n δ r) r := by
    simpa [factor, mul_comm] using hI.exp
  have hgap := gap_hasDerivAt n hn hr
  have hproduct := hfactor.mul hgap
  convert hproduct using 1
  dsimp [K]
  ring

private theorem gap_small_pos (n : ℕ) (hn : 2 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε → 0 < gap n r := by
  have hn2 : 2 ≤ n + 2 := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hlimit : Tendsto (fun r : ℝ => gap n r / r) (𝓝[>] (0 : ℝ))
      (𝓝 (1 / (n : ℝ) - 1 / ((n : ℝ) + 2))) := by
    convert (DFL.orientationMean_div_tendsto_zero_right n hn).sub
      (DFL.orientationMean_div_tendsto_zero_right (n + 2) hn2) using 1
    · ext r; simp only [gap]; ring
    · push_cast; rfl
  have hlimpos : 0 < 1 / (n : ℝ) - 1 / ((n : ℝ) + 2) := by
    apply sub_pos.mpr
    exact one_div_lt_one_div_of_lt hnR (by linarith)
  have hevent : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < gap n r / r :=
    hlimit.eventually (Ioi_mem_nhds hlimpos)
  obtain ⟨ε, hε, hsmall⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hevent
  refine ⟨ε, hε, ?_⟩
  intro r hr hrε
  have hratio : 0 < gap n r / r := hsmall ⟨hr, hrε⟩
  exact (div_pos_iff_of_pos_right hr).1 hratio

/-- For every positive field the original DFL orientation mean strictly
decreases when the embedding dimension rises by two. -/
theorem orientationMean_dimension_shift (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) :
    DFL.orientationMean (n + 2) r < DFL.orientationMean n r := by
  obtain ⟨ε, hε, hsmall⟩ := gap_small_pos n hn
  let δ : ℝ := min (r / 2) (ε / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδr : δ < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hgapδ : 0 < gap n δ := hsmall δ hδ hδε
  have hKδ : 0 < K n δ δ := mul_pos (factor_pos n δ δ) hgapδ
  have hmono : StrictMonoOn (K n δ) (Ici δ) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici δ)
    · intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hδ hx
      exact (K_hasDerivAt n hn hδ hxpos).continuousAt.continuousWithinAt
    · intro x hx
      have hxδ : δ < x := by simpa only [interior_Ici, mem_Ioi] using hx
      have hxpos : 0 < x := lt_trans hδ hxδ
      rw [(K_hasDerivAt n hn hδ hxpos).deriv]
      exact mul_pos (factor_pos n δ x) (source_pos n hn hxpos)
  have hKlt : K n δ δ < K n δ r :=
    hmono (by simp) (by simpa using le_of_lt hδr) hδr
  have hKpos : 0 < K n δ r := lt_trans hKδ hKlt
  have hgap : 0 < gap n r := by
    by_contra h
    have hle : gap n r ≤ 0 := le_of_not_gt h
    have hprod : factor n δ r * gap n r ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (factor_pos n δ r).le hle
    exact (not_le_of_gt hKpos) hprod
  simpa only [gap, sub_pos] using hgap

end

end DFL.Hysteresis.DimensionShift
