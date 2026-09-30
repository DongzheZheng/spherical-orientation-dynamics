import DFL.Geometry.SuccBetaSymmetry
import DFL.Geometry.SuccLawSymmetry
import DFL.Geometry.SuccEquatorNull
import DFL.Probability.SymmetricTailUniqueness
import DFL.Probability.PositiveTailAtZero

/-!
# Full Borel law of the actual sphere coordinate, ambient dimension at least three

The genuine positive cap formula, reflection symmetry, and zero equator
atom identify the original pushforward with an independently defined
beta-density measure.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped ENNReal

noncomputable section

def sphereBetaConst (k : ℕ) : ℝ :=
  ((k + 2 : ℕ) : ℝ) * gammaBallConst (k + 2)

theorem sphereBetaConst_pos (k : ℕ) : 0 < sphereBetaConst k := by
  unfold sphereBetaConst
  exact mul_pos (by positivity) (gammaBallConst_pos (k + 2))

private theorem coordinateLaw_succ_positive_tail_eq_beta (k : ℕ)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    coordinateLaw (k + 3) (by omega) (Set.Ioi t) =
      (ENNReal.ofReal (sphereBetaConst k) • betaCoordinateMeasure k)
        (Set.Ioi t) := by
  letI : IsFiniteMeasure (area (k + 3)) := by
    change IsFiniteMeasure (volume : Measure (Ambient (k + 3))).toSphere
    infer_instance
  haveI : IsFiniteMeasure (coordinateLaw (k + 3) (by omega)) := by
    change IsFiniteMeasure ((area (k + 3)).map
      (coordinate (k + 3) (by omega)))
    infer_instance
  haveI : IsFiniteMeasure
      (ENNReal.ofReal (sphereBetaConst k) • betaCoordinateMeasure k) :=
    Measure.smul_finite (betaCoordinateMeasure k) ENNReal.ofReal_ne_top
  apply (measureReal_eq_measureReal_iff (by finiteness) (by finiteness)).mp
  have hsource := coordinateLaw_succ_Ioi_beta_real k t ht ht1
  have htarget := betaCoordinateMeasure_Ioi_real k t ht ht1
  rw [measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal (sphereBetaConst_pos k).le,
    htarget, hsource]
  rfl

private theorem coordinateLaw_succ_eq_smul_beta_of_zero_tail (k : ℕ)
    (hzeroTail :
      coordinateLaw (k + 3) (by omega) (Set.Ioi (0 : ℝ)) =
        (ENNReal.ofReal (sphereBetaConst k) • betaCoordinateMeasure k)
          (Set.Ioi (0 : ℝ))) :
    coordinateLaw (k + 3) (by omega) =
      ENNReal.ofReal (sphereBetaConst k) • betaCoordinateMeasure k := by
  let μ := coordinateLaw (k + 3) (by omega : 0 < k + 3)
  let ν := ENNReal.ofReal (sphereBetaConst k) • betaCoordinateMeasure k
  letI : IsFiniteMeasure (area (k + 3)) := by
    change IsFiniteMeasure (volume : Measure (Ambient (k + 3))).toSphere
    infer_instance
  haveI : IsFiniteMeasure μ := by
    change IsFiniteMeasure ((area (k + 3)).map
      (coordinate (k + 3) (by omega)))
    infer_instance
  haveI : IsFiniteMeasure ν :=
    Measure.smul_finite (betaCoordinateMeasure k) ENNReal.ofReal_ne_top
  have hμsym : μ.map (fun x : ℝ => -x) = μ := by
    simpa [μ, Nat.add_assoc] using coordinateLaw_succ_map_neg (k + 2)
  have hνsym : ν.map (fun x : ℝ => -x) = ν := by
    dsimp [ν]
    rw [Measure.map_smul, betaCoordinateMeasure_map_neg]
  have hμzero : μ ({0} : Set ℝ) = 0 := by
    simpa [μ, Nat.add_assoc] using
      coordinateLaw_succ_singleton_zero (k + 2)
  have hνzero : ν ({0} : Set ℝ) = 0 := by
    simp [ν]
  have hμoutside : μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
    simpa [μ] using coordinateLaw_outside_Icc (k + 3) (by omega)
  have hβoutside : betaCoordinateMeasure k
      (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
    rw [betaCoordinateMeasure,
      Measure.restrict_apply measurableSet_Icc.compl]
    simp
  have hνoutside : ν (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
    simp [ν, hβoutside]
  have htail : ∀ t : ℝ, 0 ≤ t → μ (Set.Ioi t) = ν (Set.Ioi t) := by
    intro t ht
    rcases eq_or_lt_of_le ht with heq | hpos
    · subst t
      exact hzeroTail
    · by_cases ht1 : t < 1
      · exact coordinateLaw_succ_positive_tail_eq_beta k t hpos ht1
      · have hhigh : 1 ≤ t := le_of_not_gt ht1
        have hsub : Set.Ioi t ⊆ (Set.Icc (-1 : ℝ) 1)ᶜ := by
          intro x hx
          simp only [Set.mem_compl_iff, Set.mem_Icc, not_and]
          intro hlow
          change t < x at hx
          linarith
        rw [measure_mono_null hsub hμoutside,
          measure_mono_null hsub hνoutside]
  exact DFL.Probability.eq_of_symmetric_nonnegative_tails
    μ ν hμsym hνsym hμzero hνzero htail

/-- Complete beta-density law for the first coordinate of the original
cone-induced sphere area in every ambient dimension at least three. This
is an equality of Borel measures, including the equator and both poles. -/
theorem coordinateLaw_succ_eq_smul_beta (k : ℕ) :
    coordinateLaw (k + 3) (by omega) =
      ENNReal.ofReal (sphereBetaConst k) • betaCoordinateMeasure k := by
  apply coordinateLaw_succ_eq_smul_beta_of_zero_tail k
  apply DFL.Probability.Ioi_zero_eq_of_positive_tails
  intro t ht ht1
  exact coordinateLaw_succ_positive_tail_eq_beta k t ht ht1

end

end DFL.Geometry
