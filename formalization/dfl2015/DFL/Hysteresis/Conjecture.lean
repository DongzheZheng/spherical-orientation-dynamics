import DFL.Hysteresis.SmallFieldSign
import DFL.Hysteresis.OriginalCrossing
import DFL.Hysteresis.UnimodalFromSigns

/-!
# Formula-level DFL 2015 single-valley conjecture

The root theorem uses the one-dimensional first-coordinate marginal written
explicitly in the DFL paper and formalized in `DFL.Targets`.  The separate
geometric theorem identifying it with the pushforward of the paper's sphere
measure has not yet been formalized; see `DFL/GEOMETRIC_BRIDGE_STATUS.md`.
-/

namespace DFL

/-- The historical Section 4.3 single-valley statement for the DFL
first-coordinate integral formula, in every dimension `n ≥ 2`. -/
theorem dfl2015_unimodality_formula : DFL2015UnimodalityConjecture := by
  intro n hn
  have hsmall : ∃ δ : ℝ, 0 < δ ∧
      ∀ r : ℝ, 0 < r → r ≤ δ →
        Hysteresis.OriginalTrajectory.H n r < 0 := by
    refine ⟨(1 / 8 : ℝ), by norm_num, ?_⟩
    intro r hr hrδ
    exact Hysteresis.SmallFieldSign.original_H_neg_small n hn hr
      (lt_of_le_of_lt hrδ (by norm_num))
  obtain ⟨rstar, hrstar, hzero, hneg, hpos, _, _⟩ :=
    Hysteresis.OriginalCrossing.crossing_of_small_negative n hn hsmall
  exact Hysteresis.isUnimodal_of_original_H_signs n hn hrstar hzero hneg hpos

end DFL
