import Mathlib

/-!
# Positive-root comparison in the zero-direction lemma

The paper's zero-direction test uses the unique positive solution of
`y * (y + m) = r²` and compares it with a positive rational expression `z`.
This module checks the comparison algebra, including the direction of every
strict inequality.  Identifying `y`, `z`, and `m` with the actual spherical
mean trajectory is a separate obligation.
-/

namespace DFL.Hysteresis.PositiveRoot

noncomputable def thresholdRatio (r z m : ℝ) : ℝ :=
  r ^ 2 / (z * (z + m))

theorem root_lt_test {r y z m : ℝ}
    (hy : 0 < y) (hz : 0 < z) (hm : 0 < m)
    (hroot : y * (y + m) = r ^ 2) :
    y < z ↔ thresholdRatio r z m < 1 := by
  have hden : 0 < z * (z + m) := mul_pos hz (by linarith)
  unfold thresholdRatio
  rw [div_lt_iff₀ hden]
  constructor
  · intro hyz
    have hprod : 0 < (z - y) * (y + z + m) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  · intro hq
    by_contra hnot
    have hzy : z ≤ y := le_of_not_gt hnot
    have hprod : 0 ≤ (y - z) * (y + z + m) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

theorem root_gt_test {r y z m : ℝ}
    (hy : 0 < y) (hz : 0 < z) (hm : 0 < m)
    (hroot : y * (y + m) = r ^ 2) :
    z < y ↔ 1 < thresholdRatio r z m := by
  have hden : 0 < z * (z + m) := mul_pos hz (by linarith)
  unfold thresholdRatio
  rw [lt_div_iff₀ hden]
  constructor
  · intro hzy
    have hprod : 0 < (y - z) * (y + z + m) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  · intro hq
    by_contra hnot
    have hyz : y ≤ z := le_of_not_gt hnot
    have hprod : 0 ≤ (z - y) * (y + z + m) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

theorem root_eq_test {r y z m : ℝ}
    (hy : 0 < y) (hz : 0 < z) (hm : 0 < m)
    (hroot : y * (y + m) = r ^ 2) :
    y = z ↔ thresholdRatio r z m = 1 := by
  constructor
  · intro hyz
    subst z
    unfold thresholdRatio
    rw [← hroot]
    exact div_self (ne_of_gt (mul_pos hy (by linarith : 0 < y + m)))
  · intro hq
    rcases lt_trichotomy y z with h | h | h
    · have := (root_lt_test hy hz hm hroot).mp h
      linarith
    · exact h
    · have := (root_gt_test hy hz hm hroot).mp h
      linarith

end DFL.Hysteresis.PositiveRoot
