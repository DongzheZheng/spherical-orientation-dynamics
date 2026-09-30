import DFL.Geometry.SuccCapBeta

/-!
# Independent beta-density comparison measure

This measure is defined from Lebesgue density, independently of the
original sphere-coordinate pushforward. The first result computes its
positive upper tail in the same interval-integral form as the genuine
geometric cap law.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped ENNReal Interval

noncomputable section

def betaCoordinateMeasure (k : ℕ) : Measure ℝ :=
  (((volume : Measure ℝ).withDensity
    (fun s : ℝ => ENNReal.ofReal (betaPower k s))).restrict
      (Set.Icc (-1) 1))

private theorem betaPower_continuous (k : ℕ) : Continuous (betaPower k) := by
  unfold betaPower
  fun_prop

private theorem betaPower_nonneg (k : ℕ) (s : ℝ) :
    0 ≤ betaPower k s := by
  unfold betaPower
  positivity

instance (k : ℕ) : IsFiniteMeasure (betaCoordinateMeasure k) := by
  refine ⟨?_⟩
  change (((volume : Measure ℝ).withDensity
    (fun s : ℝ => ENNReal.ofReal (betaPower k s))).restrict
      (Set.Icc (-1) 1)) Set.univ < ∞
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    withDensity_apply _ measurableSet_Icc]
  have hint : IntegrableOn (betaPower k) (Set.Icc (-1 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1
      ((betaPower_continuous k).intervalIntegrable (-1) 1)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (-1 : ℝ) 1)] betaPower k :=
    Filter.Eventually.of_forall (betaPower_nonneg k)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  exact ENNReal.ofReal_lt_top

instance (k : ℕ) : NoAtoms (betaCoordinateMeasure k) := by
  unfold betaCoordinateMeasure
  infer_instance

/-- The independently defined beta-density measure has the expected
strict positive upper tail, with no normalization borrowed from the
original sphere measure. -/
theorem betaCoordinateMeasure_Ioi_real (k : ℕ) (t : ℝ)
    (ht : 0 < t) (ht1 : t < 1) :
    (betaCoordinateMeasure k).real (Set.Ioi t) =
      ∫ s in t..1, betaPower k s := by
  have hset : Set.Ioi t ∩ Set.Icc (-1 : ℝ) 1 = Set.Ioc t 1 := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc,
      Set.mem_Ioc]
    constructor
    · rintro ⟨hst, -, hs1⟩
      exact ⟨hst, hs1⟩
    · rintro ⟨hst, hs1⟩
      exact ⟨hst, by linarith, hs1⟩
  have hint : IntegrableOn (betaPower k) (Set.Ioc t 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht1.le).1
      ((betaPower_continuous k).intervalIntegrable t 1)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc t 1)] betaPower k :=
    Filter.Eventually.of_forall (betaPower_nonneg k)
  change ((betaCoordinateMeasure k) (Set.Ioi t)).toReal = _
  rw [betaCoordinateMeasure, Measure.restrict_apply measurableSet_Ioi,
    hset, withDensity_apply _ measurableSet_Ioc]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  have hIntNonneg : 0 ≤ ∫ s in Set.Ioc t 1, betaPower k s :=
    integral_nonneg_of_ae hnonneg
  rw [ENNReal.toReal_ofReal hIntNonneg]
  rw [← intervalIntegral.integral_of_le ht1.le]

end

end DFL.Geometry
