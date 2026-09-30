import Mathlib

/-!
The rational part of the zero-direction argument in `hysteresis.tex`,
Lemma `hyst:zero-direction`.  Here `χ = sqrt (1 + 4r) > 1` and
`A = 2n - 1`; `u = z/r` and `v = m/r` in the paper's notation.
The connection to the nonlinear ODE is outside this module.
-/

namespace DFL.Hysteresis.ZeroDirection

/-- The paper's `A = 2n - 1`. -/
def A (n : ℕ) : ℝ := 2 * (n : ℝ) - 1

/-- The paper's `z/r`, expressed in the variable `χ`. -/
noncomputable def u (n : ℕ) (χ : ℝ) : ℝ :=
  (A n + 2 / χ + 1 / χ ^ 2) / (χ + 1) ^ 2

/-- The paper's `m/r`, expressed in the variable `χ`. -/
noncomputable def v (n : ℕ) (χ : ℝ) : ℝ :=
  2 * (A n + 1 / χ) / (χ ^ 2 - 1)

/-- The product whose crossing through one determines the direction of `F(r,0)`. -/
noncomputable def q (n : ℕ) (χ : ℝ) : ℝ := u n χ * (u n χ + v n χ)

/-- The paper's `B(χ) = 1 / ((z/r) ((z/r) + (m/r)))`. -/
noncomputable def B (n : ℕ) (χ : ℝ) : ℝ := 1 / q n χ

private theorem A_pos (n : ℕ) (hn : 2 ≤ n) : 0 < A n := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  unfold A
  linarith

theorem u_pos (n : ℕ) (hn : 2 ≤ n) {χ : ℝ} (hχ : 1 < χ) : 0 < u n χ := by
  have hA := A_pos n hn
  unfold u
  positivity

theorem v_pos (n : ℕ) (hn : 2 ≤ n) {χ : ℝ} (hχ : 1 < χ) : 0 < v n χ := by
  have hA := A_pos n hn
  unfold v
  have hχ2 : 1 < χ ^ 2 := by nlinarith
  have hden : 0 < χ ^ 2 - 1 := by linarith
  have hnum : 0 < 2 * (A n + 1 / χ) := by positivity
  exact div_pos hnum hden

/-- `z/r` is strictly decreasing on the entire physical range `χ > 1`. -/
theorem u_strictAnti (n : ℕ) (hn : 2 ≤ n) {x y : ℝ}
    (hx : 1 < x) (hxy : x < y) : u n y < u n x := by
  have hy : 1 < y := by linarith
  have hA := A_pos n hn
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hinv : 1 / y < 1 / x := one_div_lt_one_div_of_lt hx0 hxy
  have hsq : x ^ 2 < y ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hxy) (by linarith : 0 < x + y)]
  have hinv2 : 1 / y ^ 2 < 1 / x ^ 2 :=
    one_div_lt_one_div_of_lt (by positivity) hsq
  have htwo : 2 / y < 2 / x := by
    calc
      2 / y = 2 * (1 / y) := by ring
      _ < 2 * (1 / x) := by nlinarith [hinv]
      _ = 2 / x := by ring
  have hnum : A n + 2 / y + 1 / y ^ 2 < A n + 2 / x + 1 / x ^ 2 := by
    linarith
  have hnx : 0 < A n + 2 / x + 1 / x ^ 2 := by positivity
  have hdx : 0 < (x + 1) ^ 2 := by positivity
  have hdy : 0 < (y + 1) ^ 2 := by positivity
  have hden : (x + 1) ^ 2 < (y + 1) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hxy) (by linarith : 0 < x + y + 2)]
  unfold u
  apply (div_lt_div_iff₀ hdy hdx).2
  have hleft := mul_lt_mul_of_pos_right hnum hdx
  have hright := mul_lt_mul_of_pos_left hden hnx
  linarith

/-- `m/r` is strictly decreasing on the entire physical range `χ > 1`. -/
theorem v_strictAnti (n : ℕ) (hn : 2 ≤ n) {x y : ℝ}
    (hx : 1 < x) (hxy : x < y) : v n y < v n x := by
  have hy : 1 < y := by linarith
  have hA := A_pos n hn
  have hx0 : 0 < x := by linarith
  have hinv : 1 / y < 1 / x := one_div_lt_one_div_of_lt hx0 hxy
  have hnum : 2 * (A n + 1 / y) < 2 * (A n + 1 / x) := by nlinarith
  have hnx : 0 < 2 * (A n + 1 / x) := by positivity
  have hdx : 0 < x ^ 2 - 1 := by nlinarith
  have hdy : 0 < y ^ 2 - 1 := by nlinarith
  have hden : x ^ 2 - 1 < y ^ 2 - 1 := by
    nlinarith [mul_pos (sub_pos.mpr hxy) (by linarith : 0 < x + y)]
  unfold v
  apply (div_lt_div_iff₀ hdy hdx).2
  have hleft := mul_lt_mul_of_pos_right hnum hdx
  have hright := mul_lt_mul_of_pos_left hden hnx
  linarith

/-- The equation `u (u + v) = 1` has at most one physical solution. -/
theorem q_strictAnti (n : ℕ) (hn : 2 ≤ n) {x y : ℝ}
    (hx : 1 < x) (hxy : x < y) : q n y < q n x := by
  have hy : 1 < y := by linarith
  have hu := u_strictAnti n hn hx hxy
  have hv := v_strictAnti n hn hx hxy
  have hux := u_pos n hn hx
  have huy := u_pos n hn hy
  have hvy := v_pos n hn hy
  have hsum : u n y + v n y < u n x + v n x := add_lt_add hu hv
  unfold q
  exact lt_trans
    (mul_lt_mul_of_pos_right hu (by linarith : 0 < u n y + v n y))
    (mul_lt_mul_of_pos_left hsum hux)

theorem q_pos (n : ℕ) (hn : 2 ≤ n) {χ : ℝ} (hχ : 1 < χ) : 0 < q n χ := by
  unfold q
  exact mul_pos (u_pos n hn hχ) (add_pos (u_pos n hn hχ) (v_pos n hn hχ))

theorem q_eq_one_unique (n : ℕ) (hn : 2 ≤ n) {x y : ℝ}
    (hx : 1 < x) (hy : 1 < y) (hqx : q n x = 1) (hqy : q n y = 1) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · have h := q_strictAnti n hn hx hxy
    rw [hqx, hqy] at h
    linarith
  · exact hxy
  · have h := q_strictAnti n hn hy hyx
    rw [hqx, hqy] at h
    linarith

theorem q_gt_one_left (n : ℕ) (hn : 2 ≤ n) {x χ₀ : ℝ}
    (hx : 1 < x) (horder : x < χ₀) (hroot : q n χ₀ = 1) : 1 < q n x := by
  calc
    1 = q n χ₀ := hroot.symm
    _ < q n x := q_strictAnti n hn hx horder

theorem q_lt_one_right (n : ℕ) (hn : 2 ≤ n) {χ₀ x : ℝ}
    (hχ₀ : 1 < χ₀) (horder : χ₀ < x) (hroot : q n χ₀ = 1) : q n x < 1 := by
  calc
    q n x < q n χ₀ := q_strictAnti n hn hχ₀ horder
    _ = 1 := hroot

theorem B_lt_one_left (n : ℕ) (hn : 2 ≤ n) {x χ₀ : ℝ}
    (hx : 1 < x) (horder : x < χ₀) (hroot : q n χ₀ = 1) : B n x < 1 := by
  have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1)
    (q_gt_one_left n hn hx horder hroot)
  simpa [B] using h

theorem B_gt_one_right (n : ℕ) (hn : 2 ≤ n) {χ₀ x : ℝ}
    (hχ₀ : 1 < χ₀) (horder : χ₀ < x) (hroot : q n χ₀ = 1) : 1 < B n x := by
  have hx : 1 < x := by linarith
  have h := one_div_lt_one_div_of_lt (q_pos n hn hx)
    (q_lt_one_right n hn hχ₀ horder hroot)
  simpa [B] using h

private theorem A_ge_three (n : ℕ) (hn : 2 ≤ n) : 3 ≤ A n := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  unfold A
  linarith

/-- An explicit point above the crossing, uniformly in `n ≥ 2`. -/
theorem q_two_gt_one (n : ℕ) (hn : 2 ≤ n) : 1 < q n 2 := by
  have hA := A_ge_three n hn
  have hu : u n 2 = (4 * A n + 5) / 36 := by
    unfold u
    norm_num
    ring
  have hv : v n 2 = (2 * A n + 1) / 3 := by
    unfold v
    norm_num
    ring
  rw [q, hu, hv]
  nlinarith [mul_nonneg (by linarith : 0 ≤ A n - 3)
    (by linarith : 0 ≤ 112 * A n + 544)]

/-- The larger explicit endpoint `A + 1` is already below the crossing. -/
theorem q_A_add_one_lt_one (n : ℕ) (hn : 2 ≤ n) : q n (A n + 1) < 1 := by
  have hA := A_ge_three n hn
  let t : ℝ := A n + 1
  have ht : 4 ≤ t := by dsimp [t]; linarith
  have htpos : 0 < t := by linarith
  have ht2pos : 0 < t ^ 2 := by positivity
  have hinv : 1 / t < 1 := (div_lt_iff₀ htpos).2 (by linarith)
  have hinv2 : 1 / t ^ 2 < 1 := (div_lt_iff₀ ht2pos).2 (by nlinarith)
  have htwo : 2 / t < 2 := (div_lt_iff₀ htpos).2 (by linarith)
  have hnumu : A n + 2 / t + 1 / t ^ 2 < A n + 3 := by linarith
  have hdenu : 0 < (t + 1) ^ 2 := by positivity
  have hu : u n t < 1 / 2 := by
    unfold u
    apply (div_lt_iff₀ hdenu).2
    dsimp [t] at *
    nlinarith [sq_nonneg (A n - 3)]
  have hnumv : 2 * (A n + 1 / t) < 2 * (A n + 1) := by nlinarith
  have hdenv : 0 < t ^ 2 - 1 := by nlinarith
  have hv : v n t < 1 := by
    unfold v
    apply (div_lt_iff₀ hdenv).2
    dsimp [t] at *
    nlinarith [sq_nonneg (A n - 3)]
  have hut : 0 < u n t := u_pos n hn (by linarith)
  have hsum : u n t + v n t < 3 / 2 := by linarith
  have hfirst := mul_lt_mul_of_pos_left hsum hut
  have hsecond := mul_lt_mul_of_pos_right hu (by norm_num : (0 : ℝ) < 3 / 2)
  change u n t * (u n t + v n t) < 1
  nlinarith

private theorem q_continuousOn (n : ℕ) :
    ContinuousOn (q n) (Set.Icc 2 (A n + 1)) := by
  intro x hx
  have hx2 : (2 : ℝ) ≤ x := hx.1
  have hx0 : x ≠ 0 := by linarith
  have hxpow : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
  have hdenu : (x + 1) ^ 2 ≠ 0 := by positivity
  have hdenv : x ^ 2 - 1 ≠ 0 := by nlinarith
  have hqAt : ContinuousAt (q n) x := by
    unfold q u v
    fun_prop (disch := assumption)
  exact hqAt.continuousWithinAt

/-- Unique crossing of the exact rational product from `hyst:zero-direction`. -/
theorem existsUnique_q_eq_one (n : ℕ) (hn : 2 ≤ n) :
    ∃! χ : ℝ, 1 < χ ∧ q n χ = 1 := by
  have hA := A_ge_three n hn
  have hab : (2 : ℝ) ≤ A n + 1 := by linarith
  have hmem : (1 : ℝ) ∈ Set.Icc (q n (A n + 1)) (q n 2) :=
    ⟨le_of_lt (q_A_add_one_lt_one n hn), le_of_lt (q_two_gt_one n hn)⟩
  obtain ⟨χ, hχ, hq⟩ := (intermediate_value_Icc' hab (q_continuousOn n)) hmem
  refine ⟨χ, ⟨by linarith [hχ.1], hq⟩, ?_⟩
  intro y hy
  exact q_eq_one_unique n hn (x := y) (y := χ) hy.1
    (by linarith [hχ.1]) hy.2 hq

end DFL.Hysteresis.ZeroDirection
