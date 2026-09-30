import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Topology.Compactness.LocallyCompact

/-! Standard smooth-test density with support in a prescribed open set.
This is the usual regular-measure compact approximation, followed by the
mathlib smooth approximation which preserves support. -/

namespace DFL.GCI
open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
noncomputable section

/-- Continuous compactly supported tests whose support stays strictly inside
`U` are dense for any regular measure concentrated on `U`. -/
theorem exists_continuous_interior_eLpNorm_sub_le
    (μ : Measure ℝ) [μ.Regular] [IsFiniteMeasureOnCompacts μ]
    (U : Set ℝ) (hU : IsOpen U) (hμU : ∀ᵐ x ∂μ, x ∈ U)
    (f : ℝ → ℝ) (hf : MemLp f 2 μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : ℝ → ℝ, HasCompactSupport g ∧ tsupport g ⊆ U ∧
      Continuous g ∧ MemLp g 2 μ ∧ eLpNorm (f - g) 2 μ ≤ ε := by
  suffices H : ∃ g : ℝ → ℝ, eLpNorm (f - g) 2 μ ≤ ε ∧
      Continuous g ∧ MemLp g 2 μ ∧ HasCompactSupport g ∧ tsupport g ⊆ U by
    rcases H with ⟨g, hg, hd, hm, hc, hs⟩
    exact ⟨g, hc, hs, hd, hm, hg⟩
  apply hf.induction_dense (by norm_num) _ _ _ _ hε
  rotate_left
  · rintro f g ⟨hf, hmf, hcf, hsf⟩ ⟨hg, hmg, hcg, hsg⟩
    exact ⟨hf.add hg, hmf.add hmg, hcf.add hcg,
      (tsupport_add f g).trans (union_subset hsf hsg)⟩
  · rintro f ⟨_, hmf, _, _⟩
    exact hmf.aestronglyMeasurable
  intro c t ht htμ ε hε
  let t₀ := t ∩ U
  have ht₀ : MeasurableSet t₀ := ht.inter hU.measurableSet
  have ht₀μ : μ t₀ < ⊤ := (measure_mono inter_subset_left).trans_lt htμ
  have hind : (t₀.indicator fun _ => c) =ᵐ[μ] (t.indicator fun _ => c) := by
    filter_upwards [hμU] with x hx
    by_cases hxt : x ∈ t <;> simp [t₀, hxt, hx]
  rcases exists_Lp_half ℝ μ 2 hε with ⟨δ, δpos, hδ⟩
  obtain ⟨η, ηpos, hη⟩ := exists_eLpNorm_indicator_le (μ := μ) (p := 2)
    (by norm_num) c δpos.ne'
  have hηpos : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.2 ηpos
  obtain ⟨s, st, hc, hs, hμs⟩ :=
    ht₀.exists_isCompact_isClosed_diff_lt ht₀μ.ne hηpos.ne'
  have hsμ : μ s < ⊤ := (measure_mono st).trans_lt ht₀μ
  have I1 : eLpNorm ((s.indicator fun _ => c) - t₀.indicator fun _ => c) 2 μ ≤ δ := by
    rw [← eLpNorm_neg, neg_sub, ← indicator_diff st]
    exact hη _ hμs.le
  obtain ⟨k, hkc, hsk, hkU⟩ := exists_compact_between hc hU (st.trans inter_subset_right)
  obtain ⟨g, hd, I2, _, hsg, hmg⟩ :=
    exists_continuous_eLpNorm_sub_le_of_closed (μ := μ) (p := 2) (by norm_num)
      hs isOpen_interior hsk hsμ.ne c δpos.ne'
  have I3 : eLpNorm (g - t₀.indicator fun _ => c) 2 μ ≤ ε := by
    convert (hδ _ _
      (hmg.aestronglyMeasurable.sub (aestronglyMeasurable_const.indicator hs.measurableSet))
      ((aestronglyMeasurable_const.indicator hs.measurableSet).sub
        (aestronglyMeasurable_const.indicator ht₀)) I2 I1).le using 2
    simp only [sub_add_sub_cancel]
  have hsgk : Function.support g ⊆ k := hsg.trans interior_subset
  have htgk : tsupport g ⊆ k := closure_minimal hsgk hkc.isClosed
  refine ⟨g, ?_, hd, hmg, HasCompactSupport.of_support_subset_isCompact hkc hsgk,
    htgk.trans hkU⟩
  have heq : (g - t₀.indicator fun _ => c) =ᵐ[μ] (g - t.indicator fun _ => c) := by
    filter_upwards [hind] with x hx
    simp only [Pi.sub_apply, hx]
  rwa [eLpNorm_congr_ae heq] at I3

/-- The library smooth approximation preserves the support of the input. -/
theorem exists_support_preserving_smooth_eLpNorm_sub_le
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (f : ℝ → ℝ) (hc : HasCompactSupport f) (hd : Continuous f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ Function.support g ⊆ Function.support f ∧
      eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal ε := by
  by_cases hf : f =ᵐ[μ] 0
  · refine ⟨0, contDiff_const, by simp, ?_⟩
    simp [eLpNorm_congr_ae hf]
  have hs₁ : μ (tsupport f) ≠ ⊤ := hc.measure_lt_top.ne
  have hs₂ : 0 < (μ (tsupport f)).toReal := by
    rw [← Measure.measure_support_eq_zero_iff _] at hf
    exact ENNReal.toReal_pos (pos_mono (subset_tsupport f) (pos_of_ne_zero hf)).ne' hs₁
  let ε₁ := ε * (μ (tsupport f)).toReal ^ (-(1 / (2 : ℝ≥0∞).toReal))
  have hε₁ : 0 < ε₁ := by dsimp [ε₁]; positivity
  have hε₂ : ENNReal.ofReal ε₁ * μ (tsupport f) ^ (1 / (2 : ℝ≥0∞).toReal) ≤
      ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal hs₁, ENNReal.ofReal_rpow_of_pos hs₂,
      ← ENNReal.ofReal_mul hε₁.le, ENNReal.ofReal_le_ofReal_iff hε.le]
    dsimp [ε₁]
    rw [mul_assoc, ← Real.rpow_add hs₂, neg_add_cancel, Real.rpow_zero, mul_one]
  obtain ⟨g, hg, happ, hs⟩ := hd.exists_contDiff_approx ⊤
    (ε := fun _ => ε₁) (by fun_prop) (by intro; exact hε₁)
  refine ⟨g, hg, hs, ?_⟩
  apply (eLpNorm_sub_le_of_dist_bdd μ (by norm_num) hc.measurableSet hε₁.le
    (s := tsupport f) ?_ (subset_tsupport f) (hs.trans (subset_tsupport f))).trans hε₂
  intro x
  rw [dist_comm]
  exact (happ x).le

/-- Smooth compactly supported tests whose support stays strictly inside
`U` are dense in `L²(μ)` if `μ` is concentrated on the open set `U`. -/
theorem exists_contDiff_interior_eLpNorm_sub_le
    (μ : Measure ℝ) [μ.Regular] [IsFiniteMeasureOnCompacts μ]
    (U : Set ℝ) (hU : IsOpen U) (hμU : ∀ᵐ x ∂μ, x ∈ U)
    (f : ℝ → ℝ) (hf : MemLp f 2 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, HasCompactSupport g ∧ tsupport g ⊆ U ∧
      ContDiff ℝ ∞ g ∧ eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal ε := by
  have hε₂ : 0 < ε / 2 := by positivity
  obtain ⟨g, hc, hs, hd, hm, hg⟩ := exists_continuous_interior_eLpNorm_sub_le μ U hU hμU
    f hf (ENNReal.ofReal_pos.mpr hε₂).ne'
  obtain ⟨g₁, hd₁, hs₁, he⟩ :=
    exists_support_preserving_smooth_eLpNorm_sub_le μ g hc hd hε₂
  have hc₁ : HasCompactSupport g₁ := hc.mono hs₁
  have hs₁U : tsupport g₁ ⊆ U := (closure_mono hs₁).trans hs
  refine ⟨g₁, hc₁, hs₁U, hd₁, ?_⟩
  have hm₁ : MemLp g₁ 2 μ := hd₁.continuous.memLp_of_hasCompactSupport hc₁
  have heq : f - g₁ = (f - g) + (g - g₁) := by ext x; simp
  rw [heq]
  exact (eLpNorm_add_le (hf.aestronglyMeasurable.sub hm.aestronglyMeasurable)
    (hm.aestronglyMeasurable.sub hm₁.aestronglyMeasurable) (by norm_num)).trans
    (by simpa [← ENNReal.ofReal_add hε₂.le hε₂.le] using add_le_add hg he)

end
end DFL.GCI
