import DFL.Hysteresis.HighFieldWitness

/-!
# Crossing barriers for the original DFL trajectory

The scalar field in `OriginalTrajectory.original_H_ode` is linearized exactly
along the actual trajectory.  The positive-root constraint is retained in
the coefficient; no replacement Riccati curve is introduced.
-/

namespace DFL.Hysteresis.OriginalCrossing

open Set Filter MeasureTheory
open scoped Topology Interval
open DFL.Hysteresis.ElasticityODE
open DFL.Hysteresis.ZeroDirectionODE
open DFL.Hysteresis.OriginalTrajectory

noncomputable section

/-- Explicit divided difference of the original scalar field.  Its root
denominator is strictly positive for `n ≥ 2` and `r > 0`. -/
private def coefficient (n : ℕ) (r ζ : ℝ) : ℝ :=
  - (((n : ℝ) - 2 + 2 * a r - ζ +
    2 * Y n r (a r - ζ) *
      (1 - a r / (Y n r (a r - ζ) + Y n r (a r) + m n r))) / r)

private theorem root_denominator_pos (n : ℕ) (hn : 2 ≤ n)
    {r ζ : ℝ} (hr : 0 < r) :
    0 < Y n r (a r - ζ) + Y n r (a r) + m n r := by
  have hy₁ := Y_pos n (e := a r - ζ) hr
  have hy₀ := Y_pos n (e := a r) hr
  have hm := m_pos n hn hr
  linarith

/-- Algebraic identity behind the integrating factor, for the exact
positive quadratic root used by the original DFL spherical mean. -/
theorem F_sub_F_zero (n : ℕ) (hn : 2 ≤ n)
    {r ζ : ℝ} (hr : 0 < r) :
    F n r ζ - F n r 0 = coefficient n r ζ * ζ := by
  let y := Y n r (a r - ζ)
  let y₀ := Y n r (a r)
  let M := m n r
  let D := y + y₀ + M
  have hD : D ≠ 0 := ne_of_gt (root_denominator_pos n hn hr)
  have hrne : r ≠ 0 := ne_of_gt hr
  have hroot₁ : y * (y + M - ζ) = r ^ 2 := by
    simpa [y, M, m, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      Y_quadratic n (e := a r - ζ) hr
  have hroot₀ : y₀ * (y₀ + M) = r ^ 2 := by
    simpa [y₀, M, m] using Y_quadratic n (e := a r) hr
  have hdiff : (y - y₀) * D = ζ * y := by
    dsimp [D]
    nlinarith [hroot₁, hroot₀]
  have hdiffa : a r * ((y - y₀) * D) = a r * (ζ * y) :=
    congrArg (fun x : ℝ => a r * x) hdiff
  unfold F coefficient
  simp only [sub_zero, add_zero]
  change deriv a r - (1 / r) *
      (((n : ℝ) - 1 + a r - ζ) * (1 - a r + ζ) -
        2 * (a r - ζ) * y) -
      (deriv a r - (1 / r) *
        (((n : ℝ) - 1 + a r) * (1 - a r) - 2 * a r * y₀)) =
      - (((n : ℝ) - 2 + 2 * a r - ζ +
        2 * y * (1 - a r / D)) / r) * ζ
  field_simp
  nlinarith [hdiffa]

private theorem H_differentiableAt (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) : DifferentiableAt ℝ (H n) r := by
  let c := DFL.orientationMean n
  let g : ℝ → ℝ := fun x => a x -
    (x / c x - ((n : ℝ) - 1) - x * c x)
  have hlocal : H n =ᶠ[𝓝 r] g := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    change a x - elasticity c x = g x
    dsimp [g]
    rw [elasticity_eq n c hx
      (DFL.orientationMean_pos n hn hx)
      (DFL.orientationMean_differentiableAt n hn x)
      (DFL.orientationMean_riccati n hn hx)]
    rfl
  have hc : DifferentiableAt ℝ c r := DFL.orientationMean_differentiableAt n hn r
  have hcne : c r ≠ 0 := ne_of_gt (DFL.orientationMean_pos n hn hr)
  have ha : DifferentiableAt ℝ a r := by
    have hs : chi r ≠ 0 := ne_of_gt (by linarith [chi_gt_one hr])
    have hden : 2 * chi r ≠ 0 := by positivity
    unfold a
    exact ((chi_hasDerivAt hr).add_const 1).div
      ((chi_hasDerivAt hr).const_mul 2) hden |>.differentiableAt
  have hg : DifferentiableAt ℝ g r := by
    dsimp [g]
    exact ha.sub (((differentiableAt_id.div hc hcne).sub
      (differentiableAt_const ((n : ℝ) - 1))).sub
      (differentiableAt_id.mul hc))
  exact hg.congr_of_eventuallyEq hlocal

private def trajectoryCoefficient (n : ℕ) (r : ℝ) : ℝ :=
  coefficient n r (H n r)

private theorem trajectoryCoefficient_continuousAt (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) : ContinuousAt (trajectoryCoefficient n) r := by
  have hH : ContinuousAt (H n) r := (H_differentiableAt n hn hr).continuousAt
  have hchi : ContinuousAt chi r := by unfold chi; fun_prop
  have hchinz : chi r ≠ 0 := ne_of_gt (by linarith [chi_gt_one hr])
  have ha : ContinuousAt a r := by
    have hden : 2 * chi r ≠ 0 := by positivity
    unfold a
    exact (((chi_hasDerivAt hr).add_const 1).div
      ((chi_hasDerivAt hr).const_mul 2) hden).continuousAt
  have hm : ContinuousAt (m n) r := by
    unfold m
    fun_prop (discharger := assumption)
  have hy₁ : ContinuousAt (fun x => Y n x (a x - H n x)) r := by
    unfold Y
    fun_prop (discharger := assumption)
  have hy₀ : ContinuousAt (fun x => Y n x (a x)) r := by
    unfold Y
    fun_prop (discharger := assumption)
  have hD : ContinuousAt
      (fun x => Y n x (a x - H n x) + Y n x (a x) + m n x) r := by
    fun_prop (discharger := assumption)
  have hDne : Y n r (a r - H n r) + Y n r (a r) + m n r ≠ 0 :=
    ne_of_gt (root_denominator_pos n hn hr)
  have hrne : r ≠ 0 := ne_of_gt hr
  unfold trajectoryCoefficient coefficient
  fun_prop (discharger := assumption)

private theorem trajectoryCoefficient_continuousOn (n : ℕ) (hn : 2 ≤ n) :
    ContinuousOn (trajectoryCoefficient n) (Ioi (0 : ℝ)) := by
  intro r hr
  exact (trajectoryCoefficient_continuousAt n hn hr).continuousWithinAt

private theorem trajectoryCoefficient_intervalIntegrable (n : ℕ) (hn : 2 ≤ n)
    {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) :
    IntervalIntegrable (trajectoryCoefficient n) MeasureTheory.volume δ r := by
  have hsubset : Set.uIcc δ r ⊆ Ioi (0 : ℝ) := by
    intro x hx
    rcases le_total δ r with hle | hle
    · rw [uIcc_of_le hle] at hx
      exact lt_of_lt_of_le hδ hx.1
    · rw [uIcc_of_ge hle] at hx
      exact lt_of_lt_of_le hr hx.1
  exact ((trajectoryCoefficient_continuousOn n hn).mono hsubset).intervalIntegrable

private def factor (n : ℕ) (δ r : ℝ) : ℝ :=
  Real.exp (-(∫ u in δ..r, trajectoryCoefficient n u))

private def K (n : ℕ) (δ r : ℝ) : ℝ := factor n δ r * H n r

/-- An exact integrating-factor identity along the original spherical
trajectory.  The multiplier is positive on the positive field axis. -/
theorem K_hasDerivAt (n : ℕ) (hn : 2 ≤ n)
    {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) :
    HasDerivAt (K n δ) (factor n δ r * F n r 0) r := by
  have hcont := trajectoryCoefficient_continuousAt n hn hr
  have hint := trajectoryCoefficient_intervalIntegrable n hn hδ hr
  have hmeas : StronglyMeasurableAtFilter
      (trajectoryCoefficient n) (𝓝 r) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
      (trajectoryCoefficient_continuousOn n hn) r hr
  have hI : HasDerivAt
      (fun x : ℝ => ∫ u in δ..x, trajectoryCoefficient n u)
      (trajectoryCoefficient n r) r :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  have hfactor : HasDerivAt (factor n δ)
      (-trajectoryCoefficient n r * factor n δ r) r := by
    simpa [factor, mul_comm] using hI.neg.exp
  have hH : HasDerivAt (H n) (F n r (H n r)) r := by
    convert (H_differentiableAt n hn hr).hasDerivAt using 1
    exact (original_H_ode n hn hr).symm
  have hproduct := hfactor.mul hH
  have hlin := F_sub_F_zero n hn (ζ := H n r) hr
  convert hproduct using 1
  dsimp [trajectoryCoefficient] at *
  rw [sub_eq_iff_eq_add] at hlin
  rw [hlin]
  ring

private theorem factor_pos (n : ℕ) (δ r : ℝ) : 0 < factor n δ r := by
  unfold factor
  exact Real.exp_pos _

private theorem K_neg_iff_H_neg (n : ℕ) (δ r : ℝ) :
    K n δ r < 0 ↔ H n r < 0 := by
  unfold K
  constructor
  · intro hK
    by_contra h
    have hH : 0 ≤ H n r := le_of_not_gt h
    have hprod : 0 ≤ factor n δ r * H n r :=
      mul_nonneg (factor_pos n δ r).le hH
    exact (not_le_of_gt hK) hprod
  · exact mul_neg_of_pos_of_neg (factor_pos n δ r)

private theorem K_pos_iff_H_pos (n : ℕ) (δ r : ℝ) :
    0 < K n δ r ↔ 0 < H n r := by
  unfold K
  constructor
  · intro hK
    by_contra h
    have hH : H n r ≤ 0 := le_of_not_gt h
    have hprod : factor n δ r * H n r ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (factor_pos n δ r).le hH
    exact (not_le_of_gt hK) hprod
  · exact mul_pos (factor_pos n δ r)

private theorem K_continuousOn_Icc (n : ℕ) (hn : 2 ≤ n)
    {δ u v : ℝ} (hδ : 0 < δ) (hu : δ ≤ u) :
    ContinuousOn (K n δ) (Icc u v) := by
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le hδ (le_trans hu hx.1)
  exact (K_hasDerivAt n hn hδ hxpos).continuousAt.continuousWithinAt

private theorem K_strictAntiOn_left (n : ℕ) (hn : 2 ≤ n)
    {δ r₀ : ℝ} (hδ : 0 < δ)
    (hleft : ∀ r : ℝ, 0 < r → r < r₀ → F n r 0 < 0) :
    StrictAntiOn (K n δ) (Icc δ r₀) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc δ r₀)
    (K_continuousOn_Icc n hn hδ (le_refl δ))
  intro x hx
  have hx' : x ∈ Ioo δ r₀ := by simpa using hx
  rw [(K_hasDerivAt n hn hδ (lt_trans hδ hx'.1)).deriv]
  exact mul_neg_of_pos_of_neg (factor_pos n δ x)
    (hleft x (lt_trans hδ hx'.1) hx'.2)

private theorem K_strictMonoOn_right (n : ℕ) (hn : 2 ≤ n)
    {δ r₀ : ℝ} (hδ : 0 < δ) (hδr₀ : δ < r₀)
    (hright : ∀ r : ℝ, r₀ < r → 0 < F n r 0) :
    StrictMonoOn (K n δ) (Ici r₀) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici r₀)
  · intro x hx
    have hxpos : 0 < x := lt_trans hδ (lt_of_lt_of_le hδr₀ hx)
    exact (K_hasDerivAt n hn hδ hxpos).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Ioi r₀ := by simpa using hx
    have hxpos : 0 < x := lt_trans (lt_trans hδ hδr₀) hx'
    rw [(K_hasDerivAt n hn hδ hxpos).deriv]
    exact mul_pos (factor_pos n δ x) (hright x hx')

/-- If the actual DFL trajectory is negative on a sufficiently small
positive interval, it has exactly one positive zero.  All other inputs are
proved for the original spherical marginal: the scalar ODE, the one-time
zero-direction reversal, and a late positive value of `H`. -/
theorem crossing_of_small_negative (n : ℕ) (hn : 2 ≤ n)
    (hsmall : ∃ δ : ℝ, 0 < δ ∧
      ∀ r : ℝ, 0 < r → r ≤ δ → H n r < 0) :
    ∃ rstar : ℝ, 0 < rstar ∧ H n rstar = 0 ∧
      (∀ r : ℝ, 0 < r → r < rstar → H n r < 0) ∧
      (∀ r : ℝ, rstar < r → 0 < H n r) ∧
      0 < deriv (H n) rstar ∧
      (∀ r : ℝ, 0 < r → H n r = 0 → r = rstar) := by
  obtain ⟨r₀, hr₀, hleft, _hzero, hright⟩ := exists_zero_direction n hn
  obtain ⟨δ₀, hδ₀, hHsmall⟩ := hsmall
  let δ : ℝ := min δ₀ (r₀ / 2)
  have hδ : 0 < δ := lt_min hδ₀ (by linarith)
  have hδr₀ : δ < r₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hHδ : H n δ < 0 := hHsmall δ hδ (min_le_left _ _)
  obtain ⟨L, hr₀L, hHL⟩ := original_H_positive_arbitrarily_late n hn hr₀
  have hKδ : K n δ δ < 0 := (K_neg_iff_H_neg n δ δ).2 hHδ
  have hKL : 0 < K n δ L := (K_pos_iff_H_pos n δ L).2 hHL
  have hanti := K_strictAntiOn_left n hn hδ hleft
  have hmono := K_strictMonoOn_right n hn hδ hδr₀ hright
  have hKr₀ : K n δ r₀ < 0 := by
    have hlt : K n δ r₀ < K n δ δ :=
      hanti (left_mem_Icc.mpr hδr₀.le)
        (right_mem_Icc.mpr hδr₀.le) hδr₀
    exact lt_trans hlt hKδ
  have hcont : ContinuousOn (K n δ) (Icc r₀ L) :=
    K_continuousOn_Icc n hn hδ hδr₀.le
  have hzero : (0 : ℝ) ∈ Icc (K n δ r₀) (K n δ L) :=
    ⟨le_of_lt hKr₀, le_of_lt hKL⟩
  obtain ⟨rstar, hrI, hKzero⟩ :=
    (intermediate_value_Icc hr₀L.le hcont) hzero
  have hr₀star : r₀ < rstar := by
    rcases lt_or_eq_of_le hrI.1 with h | h
    · exact h
    · subst rstar
      exact False.elim ((ne_of_lt hKr₀) hKzero)
  have hrstarpos : 0 < rstar := lt_trans hr₀ hr₀star
  have hHstar : H n rstar = 0 := by
    have hmul : factor n δ rstar * H n rstar = 0 := hKzero
    exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt (factor_pos n δ rstar))
  have hnegative : ∀ r : ℝ, 0 < r → r < rstar → H n r < 0 := by
    intro r hr hrstar
    by_cases hrδ : r ≤ δ
    · exact hHsmall r hr (le_trans hrδ (min_le_left _ _))
    · have hδr : δ < r := lt_of_not_ge hrδ
      have hKneg : K n δ r < 0 := by
        by_cases hrr₀ : r < r₀
        · have hlt : K n δ r < K n δ δ :=
            hanti (left_mem_Icc.mpr hδr₀.le)
              ⟨hδr.le, hrr₀.le⟩ hδr
          exact lt_trans hlt hKδ
        · have hlt : K n δ r < K n δ rstar :=
            hmono (le_of_not_gt hrr₀) hr₀star.le hrstar
          simpa only [hKzero] using hlt
      exact (K_neg_iff_H_neg n δ r).1 hKneg
  have hpositive : ∀ r : ℝ, rstar < r → 0 < H n r := by
    intro r hstarr
    have hlt : K n δ rstar < K n δ r :=
      hmono hr₀star.le (le_trans hr₀star.le hstarr.le) hstarr
    have hKpos : 0 < K n δ r := by simpa only [hKzero] using hlt
    exact (K_pos_iff_H_pos n δ r).1 hKpos
  have hder : 0 < deriv (H n) rstar := by
    rw [original_H_ode n hn hrstarpos, hHstar]
    exact hright rstar hr₀star
  have hunique : ∀ r : ℝ, 0 < r → H n r = 0 → r = rstar := by
    intro r hr hzero
    rcases lt_trichotomy r rstar with hlt | heq | hgt
    · have hneg := hnegative r hr hlt
      rw [hzero] at hneg
      exact False.elim (lt_irrefl 0 hneg)
    · exact heq
    · have hpos := hpositive r hgt
      rw [hzero] at hpos
      exact False.elim (lt_irrefl 0 hpos)
  exact ⟨rstar, hrstarpos, hHstar, hnegative, hpositive, hder, hunique⟩

/-- Every zero of the actual elasticity difference has the direction of
the proved scalar zero field, with no conditional ODE assumption. -/
theorem H_deriv_at_zero (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) (hzero : H n r = 0) :
    deriv (H n) r = F n r 0 := by
  rw [original_H_ode n hn hr, hzero]

/-- A zero beyond the unique zero-direction point crosses upward strictly. -/
theorem H_zero_deriv_pos_right (n : ℕ) (hn : 2 ≤ n)
    {r₀ r : ℝ} (hdir : ∀ x : ℝ, r₀ < x → 0 < F n x 0)
    (hr₀r : r₀ < r) (hr : 0 < r) (hzero : H n r = 0) :
    0 < deriv (H n) r := by
  rw [H_deriv_at_zero n hn hr hzero]
  exact hdir r hr₀r

end

end DFL.Hysteresis.OriginalCrossing
