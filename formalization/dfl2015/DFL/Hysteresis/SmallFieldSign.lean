import DFL.Hysteresis.MeanLinearBound
import DFL.Hysteresis.OriginalTrajectory

/-!
The original mean satisfies `c(r) < r/n` by an integrating factor. Together
with the exact feedback formula, this gives `H(r) < 0` on an explicit
small-field interval, without importing a Taylor series as an assumption.
-/

namespace DFL.Hysteresis.SmallFieldSign

open DFL.Hysteresis.ElasticityODE
open DFL.Hysteresis.ZeroDirectionODE
open DFL.Hysteresis.OriginalTrajectory

theorem one_sub_a_eq (r : ℝ) (hr : 0 < r) :
    1 - a r = 2 * r / (chi r * (chi r + 1)) := by
  have hs : chi r ≠ 0 := ne_of_gt (by linarith [chi_gt_one hr])
  have hsp : chi r + 1 ≠ 0 := by linarith [chi_gt_one hr]
  unfold a
  field_simp
  nlinarith [chi_sq hr]

theorem one_sub_a_gt_third (r : ℝ) (hr : 0 < r) (hrsmall : r < 1 / 4) :
    r / 3 < 1 - a r := by
  let s : ℝ := chi r
  have hs1 : 1 < s := chi_gt_one hr
  have hs2 : s < 2 := by nlinarith [chi_sq hr]
  have hdenpos : 0 < s * (s + 1) := by positivity
  have hdenlt : s * (s + 1) < 6 := by nlinarith [chi_sq hr]
  rw [one_sub_a_eq r hr]
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 3) hdenpos).2
  nlinarith [mul_pos hr (by linarith : 0 < 6 - s * (s + 1))]

/-- A directly verified negative initial sign for the original elasticity
difference; the numerical cutoff `1/4` is a convenient sufficient range. -/
theorem original_H_neg_small (n : ℕ) (hn : 2 ≤ n) {r : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 4) : H n r < 0 := by
  let c : ℝ → ℝ := DFL.orientationMean n
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnRpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hnRne : (n : ℝ) ≠ 0 := ne_of_gt hnRpos
  have hcpos : 0 < c r := DFL.orientationMean_pos n hn hr
  have hclt : c r < r / (n : ℝ) :=
    MeanLinearBound.orientationMean_lt_linear n hn hr
  have hnc : (n : ℝ) * c r < r := by
    calc
      (n : ℝ) * c r < (n : ℝ) * (r / (n : ℝ)) :=
        mul_lt_mul_of_pos_left hclt hnRpos
      _ = r := by field_simp
  have hratio : (n : ℝ) < r / c r := (lt_div_iff₀ hcpos).2 hnc
  have heq : elasticity c r = r / c r - ((n : ℝ) - 1) - r * c r :=
    elasticity_eq n c hr hcpos
      (DFL.orientationMean_differentiableAt n hn r)
      (DFL.orientationMean_riccati n hn hr)
  have he_lower : 1 - r * c r < elasticity c r := by rw [heq]; linarith
  have hrc : r * c r < r ^ 2 / (n : ℝ) := by
    calc
      r * c r < r * (r / (n : ℝ)) := mul_lt_mul_of_pos_left hclt hr
      _ = r ^ 2 / (n : ℝ) := by ring
  have hrdiv : r / (n : ℝ) < 1 / 3 := by
    apply (div_lt_iff₀ hnRpos).2
    nlinarith
  have hr2 : r ^ 2 / (n : ℝ) < r / 3 := by
    calc
      r ^ 2 / (n : ℝ) = r * (r / (n : ℝ)) := by ring
      _ < r * (1 / 3) := mul_lt_mul_of_pos_left hrdiv hr
      _ = r / 3 := by ring
  have ha : r / 3 < 1 - a r := one_sub_a_gt_third r hr hrsmall
  unfold H
  dsimp [c] at he_lower hrc
  linarith

end DFL.Hysteresis.SmallFieldSign
