import DFL.Geometry.SuccBetaMeasure

/-!
# Reflection symmetry of the independent beta-density measure
-/

namespace DFL.Geometry

open MeasureTheory
open scoped ENNReal

noncomputable section

theorem betaPower_neg (k : ℕ) (x : ℝ) :
    betaPower k (-x) = betaPower k x := by
  simp [betaPower]

theorem betaCoordinateMeasure_map_neg (k : ℕ) :
    (betaCoordinateMeasure k).map (fun x : ℝ => -x) =
      betaCoordinateMeasure k := by
  apply Measure.ext
  intro A hA
  let B : Set ℝ := A ∩ Set.Icc (-1) 1
  have hB : MeasurableSet B := hA.inter measurableSet_Icc
  let f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (betaPower k x)
  have hf : Measurable f := by
    dsimp [f, betaPower]
    fun_prop
  have hpre : (fun x : ℝ => -x) ⁻¹' A ∩ Set.Icc (-1 : ℝ) 1 =
      (fun x : ℝ => -x) ⁻¹' B := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc, B]
    constructor
    · rintro ⟨hAneg, hlow, hhigh⟩
      exact ⟨hAneg, by constructor <;> linarith⟩
    · rintro ⟨hAneg, hlow, hhigh⟩
      exact ⟨hAneg, by constructor <;> linarith⟩
  rw [Measure.map_apply measurable_neg hA,
    betaCoordinateMeasure,
    Measure.restrict_apply (hA.preimage measurable_neg),
    Measure.restrict_apply hA,
    hpre,
    withDensity_apply _ (hB.preimage measurable_neg),
    withDensity_apply _ hB]
  rw [← lintegral_indicator (hB.preimage measurable_neg) f,
    ← lintegral_indicator hB f]
  have hpoint (x : ℝ) :
      ((fun y : ℝ => -y) ⁻¹' B).indicator f x =
        B.indicator f (-x) := by
    by_cases hx : -x ∈ B
    · simp [Set.indicator, hx, f, betaPower_neg]
    · simp [Set.indicator, hx]
  calc
    (∫⁻ x : ℝ, ((fun y : ℝ => -y) ⁻¹' B).indicator f x) =
        ∫⁻ x : ℝ, B.indicator f (-x) := by
          apply lintegral_congr
          intro x
          exact hpoint x
    _ = ∫⁻ x : ℝ, B.indicator f x ∂
          ((volume : Measure ℝ).map (fun y : ℝ => -y)) := by
          rw [lintegral_map (hf.indicator hB) measurable_neg]
    _ = ∫⁻ x : ℝ, B.indicator f x := by
          rw [Measure.map_neg_eq_self]

end

end DFL.Geometry
