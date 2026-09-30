import DFL.Hysteresis.ZeroDirectionBridge

/-!
The exact scalar formulas in `hysteresis.tex`, equations `hyst:H-ode` through
`hyst:rational-factors`. This module relates those formulas; it does not assume
that the actual spherical mean solves the Riccati equation or that its
elasticity solves this ODE.
-/

namespace DFL.Hysteresis.ZeroDirectionODE

open DFL.Hysteresis.ZeroDirection
open DFL.Hysteresis.PositiveRoot

noncomputable def chi (r : ℝ) : ℝ := Real.sqrt (1 + 4 * r)

noncomputable def a (r : ℝ) : ℝ := (chi r + 1) / (2 * chi r)

noncomputable def m (n : ℕ) (r : ℝ) : ℝ := (n : ℝ) - 1 + a r

noncomputable def Y (n : ℕ) (r e : ℝ) : ℝ :=
  (Real.sqrt (((n : ℝ) - 1 + e) ^ 2 + 4 * r ^ 2) - ((n : ℝ) - 1 + e)) / 2

noncomputable def F (n : ℕ) (r ζ : ℝ) : ℝ :=
  deriv a r - (1 / r) *
    (((n : ℝ) - 1 + a r - ζ) * (1 - a r + ζ) -
      2 * (a r - ζ) * Y n r (a r - ζ))

noncomputable def z (n : ℕ) (r : ℝ) : ℝ :=
  (r / (chi r) ^ 3 + m n r * (1 - a r)) / (2 * a r)

theorem chi_sq {r : ℝ} (hr : 0 < r) : chi r ^ 2 = 1 + 4 * r := by
  unfold chi
  exact Real.sq_sqrt (by linarith)

theorem chi_gt_one {r : ℝ} (hr : 0 < r) : 1 < chi r := by
  have hs := chi_sq hr
  have hnonneg : 0 ≤ chi r := Real.sqrt_nonneg _
  nlinarith

theorem r_eq_chi {r : ℝ} (hr : 0 < r) : r = (chi r ^ 2 - 1) / 4 := by
  nlinarith [chi_sq hr]

theorem a_pos {r : ℝ} (hr : 0 < r) : 0 < a r := by
  have hs := chi_gt_one hr
  unfold a
  positivity

theorem chi_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt chi (2 / chi r) r := by
  have harg : 1 + 4 * r ≠ 0 := by linarith
  have hlin : HasDerivAt (fun x : ℝ => 1 + 4 * x) 4 r := by
    convert (hasDerivAt_const r (1 : ℝ)).add
      ((hasDerivAt_id r).const_mul 4) using 1
    ring
  have hchi : HasDerivAt chi (4 / (2 * chi r)) r := by
    convert hlin.sqrt harg using 1
  convert hchi using 1
  have hs : chi r ≠ 0 := ne_of_gt (by linarith [chi_gt_one hr])
  field_simp
  ring

/-- The actual derivative of the paper's feedback elasticity `a`, not an
independently stipulated symbol. -/
theorem a_deriv {r : ℝ} (hr : 0 < r) : deriv a r = -1 / (chi r) ^ 3 := by
  have hs : chi r ≠ 0 := ne_of_gt (by linarith [chi_gt_one hr])
  have hden : 2 * chi r ≠ 0 := by positivity
  have hchi := chi_hasDerivAt hr
  have hder : HasDerivAt a
      (((2 / chi r) * (2 * chi r) -
        (chi r + 1) * (2 * (2 / chi r))) / (2 * chi r) ^ 2) r := by
    unfold a
    convert (hchi.add_const 1).div (hchi.const_mul 2) hden using 1
  rw [hder.deriv]
  field_simp
  ring

theorem m_eq_chi (n : ℕ) {r : ℝ} (hr : 0 < r) :
    m n r = (A n * chi r + 1) / (2 * chi r) := by
  have hs : chi r ≠ 0 := ne_of_gt (by linarith [chi_gt_one hr])
  unfold m a A
  field_simp
  ring

theorem m_div_r_eq_v (n : ℕ) {r : ℝ} (hr : 0 < r) :
    m n r / r = v n (chi r) := by
  have hs : chi r ≠ 0 := ne_of_gt (by linarith [chi_gt_one hr])
  have hrne : r ≠ 0 := ne_of_gt hr
  have hsm : chi r ^ 2 - 1 ≠ 0 := by nlinarith [chi_sq hr]
  rw [m_eq_chi n hr]
  unfold v
  field_simp
  linear_combination (A n * chi r + 1) * (chi_sq hr)

theorem z_eq_chi_rational (n : ℕ) {r : ℝ} (hr : 0 < r) :
    z n r = (chi r - 1) * (A n * (chi r) ^ 2 + 2 * chi r + 1) /
      (4 * (chi r) ^ 2 * (chi r + 1)) := by
  let s : ℝ := chi r
  have hs1 : 1 < s := chi_gt_one hr
  have hs : s ≠ 0 := by linarith
  have hsp : s + 1 ≠ 0 := by linarith
  have hrform : r = (s ^ 2 - 1) / 4 := r_eq_chi hr
  unfold z
  rw [m_eq_chi n hr]
  unfold a
  change (r / s ^ 3 + (A n * s + 1) / (2 * s) *
      (1 - (s + 1) / (2 * s))) / (2 * ((s + 1) / (2 * s))) =
    (s - 1) * (A n * s ^ 2 + 2 * s + 1) / (4 * s ^ 2 * (s + 1))
  rw [hrform]
  field_simp
  ring

theorem z_div_r_eq_u (n : ℕ) {r : ℝ} (hr : 0 < r) :
    z n r / r = u n (chi r) := by
  let s : ℝ := chi r
  have hs1 : 1 < s := chi_gt_one hr
  have hs : s ≠ 0 := by linarith
  have hsp : s + 1 ≠ 0 := by linarith
  have hsm : s ^ 2 - 1 ≠ 0 := by nlinarith [chi_sq hr]
  have hrform : r = (s ^ 2 - 1) / 4 := r_eq_chi hr
  rw [z_eq_chi_rational n hr]
  change ((s - 1) * (A n * s ^ 2 + 2 * s + 1) /
      (4 * s ^ 2 * (s + 1))) / r = u n s
  rw [hrform]
  unfold u
  field_simp
  ring

/-- Equation `hyst:zero-direction-factor`, with `a'` computed from the
actual feedback elasticity. -/
theorem r_mul_F_zero (n : ℕ) {r : ℝ} (hr : 0 < r) :
    r * F n r 0 = 2 * a r * (Y n r (a r) - z n r) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hs : chi r ≠ 0 := ne_of_gt (by linarith [chi_gt_one hr])
  have ha : a r ≠ 0 := ne_of_gt (a_pos hr)
  unfold F z m
  rw [a_deriv hr]
  field_simp
  ring

theorem m_pos (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) : 0 < m n r := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  unfold m
  linarith [a_pos hr]

theorem Y_pos (n : ℕ) {r e : ℝ} (hr : 0 < r) : 0 < Y n r e := by
  let M : ℝ := (n : ℝ) - 1 + e
  let S : ℝ := Real.sqrt (M ^ 2 + 4 * r ^ 2)
  have harg : 0 ≤ M ^ 2 + 4 * r ^ 2 := by positivity
  have hsq : S ^ 2 = M ^ 2 + 4 * r ^ 2 := Real.sq_sqrt harg
  have hsnonneg : 0 ≤ S := Real.sqrt_nonneg _
  have hSM : M < S := by
    by_contra h
    have hMS : S ≤ M := le_of_not_gt h
    have hprod : 0 ≤ (M - S) * (M + S) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [sq_pos_of_pos hr]
  unfold Y
  change 0 < (S - M) / 2
  linarith

theorem Y_quadratic (n : ℕ) {r e : ℝ} (hr : 0 < r) :
    Y n r e * (Y n r e + ((n : ℝ) - 1 + e)) = r ^ 2 := by
  let M : ℝ := (n : ℝ) - 1 + e
  let S : ℝ := Real.sqrt (M ^ 2 + 4 * r ^ 2)
  have harg : 0 ≤ M ^ 2 + 4 * r ^ 2 := by positivity
  have hsq : S ^ 2 = M ^ 2 + 4 * r ^ 2 := Real.sq_sqrt harg
  unfold Y
  change (S - M) / 2 * ((S - M) / 2 + M) = r ^ 2
  nlinarith

theorem z_pos (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) : 0 < z n r := by
  have hzr : z n r = r * u n (chi r) := by
    calc
      z n r = (z n r / r) * r := by field_simp
      _ = r * u n (chi r) := by rw [z_div_r_eq_u n hr]; ring
  rw [hzr]
  exact mul_pos hr (u_pos n hn (chi_gt_one hr))

theorem thresholdRatio_eq_B (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) :
    thresholdRatio r (z n r) (m n r) = B n (chi r) := by
  have hz : z n r = r * u n (chi r) := by
    calc
      z n r = (z n r / r) * r := by field_simp
      _ = r * u n (chi r) := by rw [z_div_r_eq_u n hr]; ring
  have hm : m n r = r * v n (chi r) := by
    calc
      m n r = (m n r / r) * r := by field_simp
      _ = r * v n (chi r) := by rw [m_div_r_eq_v n hr]; ring
  rw [hz, hm]
  exact DFL.Hysteresis.ZeroDirectionBridge.thresholdRatio_scaled n hn
    (chi r) r (chi_gt_one hr) hr

theorem F_zero_neg_iff_B_lt_one (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) :
    F n r 0 < 0 ↔ B n (chi r) < 1 := by
  have hy : 0 < Y n r (a r) := Y_pos n hr
  have hz : 0 < z n r := z_pos n hn hr
  have hm : 0 < m n r := m_pos n hn hr
  have hroot : Y n r (a r) * (Y n r (a r) + m n r) = r ^ 2 := by
    simpa [m] using Y_quadratic n (e := a r) hr
  have hfactor := r_mul_F_zero n hr
  have hcoef : 0 < 2 * a r := by positivity [a_pos hr]
  have hsign : F n r 0 < 0 ↔ Y n r (a r) < z n r := by
    constructor
    · intro hf
      have hrf : r * F n r 0 < 0 := by nlinarith [mul_pos hr (by linarith : 0 < -F n r 0)]
      have hprod : 2 * a r * (Y n r (a r) - z n r) < 0 := by
        rw [← hfactor]
        exact hrf
      by_contra h
      have hnonneg : 0 ≤ 2 * a r * (Y n r (a r) - z n r) :=
        mul_nonneg (le_of_lt hcoef) (by linarith)
      linarith
    · intro hyz
      have hprod : 2 * a r * (Y n r (a r) - z n r) < 0 := by
        nlinarith [mul_pos hcoef (by linarith : 0 < z n r - Y n r (a r))]
      have hrf : r * F n r 0 < 0 := by rw [hfactor]; exact hprod
      by_contra h
      have hnonneg : 0 ≤ r * F n r 0 :=
        mul_nonneg (le_of_lt hr) (by linarith)
      linarith
  rw [hsign, ← thresholdRatio_eq_B n hn hr]
  exact root_lt_test hy hz hm hroot

theorem F_zero_eq_iff_B_eq_one (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) :
    F n r 0 = 0 ↔ B n (chi r) = 1 := by
  have hy : 0 < Y n r (a r) := Y_pos n hr
  have hz : 0 < z n r := z_pos n hn hr
  have hm : 0 < m n r := m_pos n hn hr
  have hroot : Y n r (a r) * (Y n r (a r) + m n r) = r ^ 2 := by
    simpa [m] using Y_quadratic n (e := a r) hr
  have hfactor := r_mul_F_zero n hr
  have hcoef : 2 * a r ≠ 0 := ne_of_gt (by nlinarith [a_pos hr])
  have hsign : F n r 0 = 0 ↔ Y n r (a r) = z n r := by
    constructor
    · intro hf
      have hprod : 2 * a r * (Y n r (a r) - z n r) = 0 := by
        rw [← hfactor, hf]
        ring
      have hdiff := (mul_eq_zero.mp hprod).resolve_left hcoef
      linarith
    · intro hyz
      have hprod : 2 * a r * (Y n r (a r) - z n r) = 0 := by rw [hyz]; ring
      have hrf : r * F n r 0 = 0 := by rw [hfactor]; exact hprod
      exact (mul_eq_zero.mp hrf).resolve_left (ne_of_gt hr)
  rw [hsign, ← thresholdRatio_eq_B n hn hr]
  exact root_eq_test hy hz hm hroot

theorem F_zero_pos_iff_B_gt_one (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) :
    0 < F n r 0 ↔ 1 < B n (chi r) := by
  have hy : 0 < Y n r (a r) := Y_pos n hr
  have hz : 0 < z n r := z_pos n hn hr
  have hm : 0 < m n r := m_pos n hn hr
  have hroot : Y n r (a r) * (Y n r (a r) + m n r) = r ^ 2 := by
    simpa [m] using Y_quadratic n (e := a r) hr
  have hfactor := r_mul_F_zero n hr
  have hcoef : 0 < 2 * a r := by nlinarith [a_pos hr]
  have hsign : 0 < F n r 0 ↔ z n r < Y n r (a r) := by
    constructor
    · intro hf
      have hrf : 0 < r * F n r 0 := mul_pos hr hf
      have hprod : 0 < 2 * a r * (Y n r (a r) - z n r) := by
        rw [← hfactor]
        exact hrf
      by_contra h
      have hnonpos : 2 * a r * (Y n r (a r) - z n r) ≤ 0 := by
        nlinarith [mul_nonneg hcoef.le (by linarith : 0 ≤ z n r - Y n r (a r))]
      linarith
    · intro hzy
      have hprod : 0 < 2 * a r * (Y n r (a r) - z n r) :=
        mul_pos hcoef (by linarith)
      have hrf : 0 < r * F n r 0 := by rw [hfactor]; exact hprod
      by_contra h
      have hnonpos : r * F n r 0 ≤ 0 := by
        nlinarith [mul_nonneg hr.le (by linarith : 0 ≤ -F n r 0)]
      linarith
  rw [hsign, ← thresholdRatio_eq_B n hn hr]
  exact root_gt_test hy hz hm hroot

theorem B_eq_one_iff_q_eq_one (n : ℕ) (hn : 2 ≤ n) {s : ℝ} (hs : 1 < s) :
    B n s = 1 ↔ q n s = 1 := by
  have hqne : q n s ≠ 0 := ne_of_gt (q_pos n hn hs)
  unfold B
  constructor
  · intro h
    have h' := (div_eq_iff hqne).mp h
    nlinarith
  · intro h
    simp [h]

theorem chi_strictMono_pos {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : r < s) :
    chi r < chi s := by
  have hχr := chi_gt_one hr
  have hχs := chi_gt_one hs
  by_contra h
  have horder : chi s ≤ chi r := le_of_not_gt h
  have hprod : 0 ≤ (chi r - chi s) * (chi r + chi s) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [chi_sq hr, chi_sq hs]

private theorem chi_of_square_minus_one {s : ℝ} (hs : 1 < s) :
    chi ((s ^ 2 - 1) / 4) = s := by
  unfold chi
  have harg : 1 + 4 * ((s ^ 2 - 1) / 4) = s ^ 2 := by ring
  rw [harg, Real.sqrt_sq (by linarith : 0 ≤ s)]

/-- The complete three-way sign pattern for the explicitly defined scalar
field `F` in `hyst:H-ode`. -/
theorem exists_zero_direction (n : ℕ) (hn : 2 ≤ n) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      (∀ r : ℝ, 0 < r → r < r₀ → F n r 0 < 0) ∧
      F n r₀ 0 = 0 ∧
      (∀ r : ℝ, r₀ < r → 0 < F n r 0) := by
  obtain ⟨s, ⟨hs, hq⟩, _⟩ := existsUnique_q_eq_one n hn
  let r₀ : ℝ := (s ^ 2 - 1) / 4
  have hr₀ : 0 < r₀ := by
    dsimp [r₀]
    nlinarith [mul_pos (sub_pos.mpr hs) (by linarith : 0 < s + 1)]
  have hχ₀ : chi r₀ = s := chi_of_square_minus_one hs
  have hB₀ : B n (chi r₀) = 1 := by rw [hχ₀]; simp [B, hq]
  refine ⟨r₀, hr₀, ?_, (F_zero_eq_iff_B_eq_one n hn hr₀).2 hB₀, ?_⟩
  · intro r hr hlt
    have hχlt : chi r < s := by
      rw [← hχ₀]
      exact chi_strictMono_pos hr hr₀ hlt
    have hBlt : B n (chi r) < 1 :=
      B_lt_one_left n hn (chi_gt_one hr) hχlt hq
    exact (F_zero_neg_iff_B_lt_one n hn hr).2 hBlt
  · intro r hlt
    have hr : 0 < r := by linarith
    have hχgt : s < chi r := by
      rw [← hχ₀]
      exact chi_strictMono_pos hr₀ hr hlt
    have hBgt : 1 < B n (chi r) :=
      B_gt_one_right n hn hs hχgt hq
    exact (F_zero_pos_iff_B_gt_one n hn hr).2 hBgt

theorem zero_direction_unique (n : ℕ) (hn : 2 ≤ n) {r₀ r₁ : ℝ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hF₀ : F n r₀ 0 = 0) (hF₁ : F n r₁ 0 = 0) : r₀ = r₁ := by
  have hB₀ := (F_zero_eq_iff_B_eq_one n hn hr₀).1 hF₀
  have hB₁ := (F_zero_eq_iff_B_eq_one n hn hr₁).1 hF₁
  have hq₀ := (B_eq_one_iff_q_eq_one n hn (chi_gt_one hr₀)).1 hB₀
  have hq₁ := (B_eq_one_iff_q_eq_one n hn (chi_gt_one hr₁)).1 hB₁
  have hχeq := q_eq_one_unique n hn (chi_gt_one hr₀) (chi_gt_one hr₁) hq₀ hq₁
  have hsqeq := congrArg (fun x : ℝ => x ^ 2) hχeq
  nlinarith [chi_sq hr₀, chi_sq hr₁]

/-- The paper's complete `hyst:zero-direction` claim, for its explicitly
defined scalar field `F`. -/
theorem existsUnique_zero_direction (n : ℕ) (hn : 2 ≤ n) :
    ∃! r₀ : ℝ, 0 < r₀ ∧ F n r₀ 0 = 0 ∧
      (∀ r : ℝ, 0 < r → r < r₀ → F n r 0 < 0) ∧
      (∀ r : ℝ, r₀ < r → 0 < F n r 0) := by
  obtain ⟨r₀, hr₀, hleft, hzero, hright⟩ := exists_zero_direction n hn
  refine ⟨r₀, ⟨hr₀, hzero, hleft, hright⟩, ?_⟩
  intro r h
  exact zero_direction_unique n hn h.1 hr₀ h.2.1 hzero

end DFL.Hysteresis.ZeroDirectionODE
