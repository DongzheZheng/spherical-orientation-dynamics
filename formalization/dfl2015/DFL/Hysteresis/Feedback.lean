import Mathlib

/-!
# The feedback law in the original DFL hysteresis example

These are exact algebraic identities for the law `k(J) = J + J²` and its
nonnegative inverse.  They do not by themselves prove the single-fold
conjecture: that theorem also depends on the original spherical mean.
-/

namespace DFL.Hysteresis

def feedback (J : ℝ) : ℝ := J + J ^ 2

noncomputable def inverseFeedback (r : ℝ) : ℝ :=
  (Real.sqrt (1 + 4 * r) - 1) / 2

theorem inverseFeedback_nonneg {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ inverseFeedback r := by
  have hrad : 0 ≤ 1 + 4 * r := by linarith
  have hs : (Real.sqrt (1 + 4 * r)) ^ 2 = 1 + 4 * r :=
    Real.sq_sqrt hrad
  have hsn : 0 ≤ Real.sqrt (1 + 4 * r) := Real.sqrt_nonneg _
  unfold inverseFeedback
  nlinarith

theorem inverseFeedback_spec {r : ℝ} (hr : 0 ≤ r) :
    feedback (inverseFeedback r) = r := by
  have hrad : 0 ≤ 1 + 4 * r := by linarith
  have hs : (Real.sqrt (1 + 4 * r)) ^ 2 = 1 + 4 * r :=
    Real.sq_sqrt hrad
  unfold feedback inverseFeedback
  nlinarith

theorem inverseFeedback_pos {r : ℝ} (hr : 0 < r) :
    0 < inverseFeedback r := by
  have hj : 0 ≤ inverseFeedback r := inverseFeedback_nonneg hr.le
  by_contra hnot
  have hjzero : inverseFeedback r = 0 := le_antisymm (le_of_not_gt hnot) hj
  have hspec := inverseFeedback_spec hr.le
  rw [hjzero] at hspec
  simp [feedback] at hspec
  linarith

theorem feedback_injective_nonneg {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : feedback a = feedback b) : a = b := by
  unfold feedback at h
  nlinarith [sq_nonneg (a - b)]

theorem inverseFeedback_unique {r J : ℝ} (hr : 0 ≤ r) (hJ : 0 ≤ J)
    (h : feedback J = r) : J = inverseFeedback r := by
  apply feedback_injective_nonneg hJ (inverseFeedback_nonneg hr)
  rw [h, inverseFeedback_spec hr]

end DFL.Hysteresis
