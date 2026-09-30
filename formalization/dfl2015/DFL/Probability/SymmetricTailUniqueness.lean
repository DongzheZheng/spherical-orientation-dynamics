import Mathlib

/-!
# Identifying symmetric real measures from positive upper tails

This measure-theoretic lemma is designed for the original spherical
coordinate pushforward.  It uses only symmetry, a zero equator atom,
and upper-tail values on the nonnegative half-line; no density is assumed.
-/

namespace DFL.Probability

open MeasureTheory

private theorem restrict_pos_eq_of_tails
    (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (htail : ∀ t : ℝ, 0 ≤ t → μ (Set.Ioi t) = ν (Set.Ioi t)) :
    μ.restrict (Set.Ioi (0 : ℝ)) = ν.restrict (Set.Ioi (0 : ℝ)) := by
  apply MeasureTheory.ext_of_generate_finite
    (Set.range (fun t : ℝ => Set.Ioi t))
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioi ℝ))
    isPiSystem_Ioi
  · rintro _ ⟨t, rfl⟩
    rw [Measure.restrict_apply measurableSet_Ioi,
      Measure.restrict_apply measurableSet_Ioi]
    by_cases ht : 0 ≤ t
    · have hs : Set.Ioi t ∩ Set.Ioi (0 : ℝ) = Set.Ioi t := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ioi]
        constructor
        · exact And.left
        · intro hx
          exact ⟨hx, lt_of_le_of_lt ht hx⟩
      rw [hs]
      exact htail t ht
    · have htn : t < 0 := lt_of_not_ge ht
      have hs : Set.Ioi t ∩ Set.Ioi (0 : ℝ) = Set.Ioi 0 := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ioi]
        constructor
        · exact And.right
        · intro hx
          exact ⟨lt_trans htn hx, hx⟩
      rw [hs]
      exact htail 0 le_rfl
  · simpa using htail 0 le_rfl

private theorem restrict_neg_eq_of_symmetry
    (μ : Measure ℝ)
    (hsym : μ.map (fun x : ℝ => -x) = μ) :
    μ.restrict (Set.Iio (0 : ℝ)) =
      (μ.restrict (Set.Ioi (0 : ℝ))).map (fun x : ℝ => -x) := by
  calc
    μ.restrict (Set.Iio (0 : ℝ)) =
        (μ.map (fun x : ℝ => -x)).restrict (Set.Iio 0) := by rw [hsym]
    _ = (μ.restrict ((fun x : ℝ => -x) ⁻¹' Set.Iio 0)).map
          (fun x : ℝ => -x) :=
      Measure.restrict_map measurable_neg measurableSet_Iio
    _ = (μ.restrict (Set.Ioi 0)).map (fun x : ℝ => -x) := by
      congr 1
      ext x
      simp

private theorem measure_eq_pos_add_neg
    (μ : Measure ℝ) (hzero : μ ({0} : Set ℝ) = 0) :
    μ = μ.restrict (Set.Ioi (0 : ℝ)) +
      μ.restrict (Set.Iio (0 : ℝ)) := by
  have hunion : (Set.Ioi (0 : ℝ)) ∪ Set.Iio 0 = ({0} : Set ℝ)ᶜ := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iio,
      Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact ne_of_gt h
      · exact ne_of_lt h
    · intro h
      rcases lt_trichotomy x 0 with hlt | heq | hgt
      · exact Or.inr hlt
      · exact False.elim (h heq)
      · exact Or.inl hgt
  have hdisj : Disjoint (Set.Ioi (0 : ℝ)) (Set.Iio 0) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    change 0 < x at hx
    change x < 0 at hy
    linarith
  calc
    μ = μ.restrict ({0} : Set ℝ) + μ.restrict ({0} : Set ℝ)ᶜ :=
      (Measure.restrict_add_restrict_compl (measurableSet_singleton 0)).symm
    _ = μ.restrict ({0} : Set ℝ)ᶜ := by
      rw [Measure.restrict_zero_set hzero, zero_add]
    _ = μ.restrict (Set.Ioi 0 ∪ Set.Iio 0) := by rw [hunion]
    _ = μ.restrict (Set.Ioi 0) + μ.restrict (Set.Iio 0) :=
      Measure.restrict_union hdisj measurableSet_Iio

/-- Finite symmetric Borel measures on the line agree everywhere once
their strict upper tails agree for every nonnegative threshold and both
give zero mass to the origin. -/
theorem eq_of_symmetric_nonnegative_tails
    (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμsym : μ.map (fun x : ℝ => -x) = μ)
    (hνsym : ν.map (fun x : ℝ => -x) = ν)
    (hμzero : μ ({0} : Set ℝ) = 0)
    (hνzero : ν ({0} : Set ℝ) = 0)
    (htail : ∀ t : ℝ, 0 ≤ t → μ (Set.Ioi t) = ν (Set.Ioi t)) :
    μ = ν := by
  have hpos := restrict_pos_eq_of_tails μ ν htail
  have hneg : μ.restrict (Set.Iio (0 : ℝ)) =
      ν.restrict (Set.Iio (0 : ℝ)) := by
    rw [restrict_neg_eq_of_symmetry μ hμsym,
      restrict_neg_eq_of_symmetry ν hνsym, hpos]
  calc
    μ = μ.restrict (Set.Ioi 0) + μ.restrict (Set.Iio 0) :=
      measure_eq_pos_add_neg μ hμzero
    _ = ν.restrict (Set.Ioi 0) + ν.restrict (Set.Iio 0) := by
      rw [hpos, hneg]
    _ = ν := (measure_eq_pos_add_neg ν hνzero).symm

end DFL.Probability
