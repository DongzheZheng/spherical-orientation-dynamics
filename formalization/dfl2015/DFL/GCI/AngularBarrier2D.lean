import DFL.GCI.AngularMoment2D

/-!
# A nonsingular supersolution for the original two-dimensional GCI operator

The exact ground profile vanishes at the angular endpoints.  A small
multiple of `cos² θ` lifts it to a strictly positive profile on the
closed interval, allowing a Picone identity without singular boundary
quotients.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def twoDGround (r θ : ℝ) : ℝ :=
  Real.sin θ * Real.exp (-(r * Real.cos θ) / 3)

def twoDLift (θ : ℝ) : ℝ :=
  (Real.cos θ) ^ 2

def twoDBarrier (r ε θ : ℝ) : ℝ :=
  twoDGround r θ + ε * twoDLift θ

def twoDOperatorValue (r θ y' y'' : ℝ) : ℝ :=
  -y'' + r * Real.sin θ * y'

private theorem twoDGround_hasDerivAt (r θ : ℝ) :
    HasDerivAt (twoDGround r)
      (Real.exp (-(r * Real.cos θ) / 3) *
        (Real.cos θ + r / 3 * (Real.sin θ) ^ 2)) θ := by
  have harg : HasDerivAt
      (fun x : ℝ => -(r * Real.cos x) / 3)
      (r * Real.sin θ / 3) θ := by
    convert (((Real.hasDerivAt_cos θ).const_mul r).neg).div_const 3 using 1
    ring
  have hprod := (Real.hasDerivAt_sin θ).mul harg.exp
  convert hprod using 1
  ring

private theorem twoDGround_deriv (r θ : ℝ) :
    deriv (twoDGround r) θ =
      Real.exp (-(r * Real.cos θ) / 3) *
        (Real.cos θ + r / 3 * (Real.sin θ) ^ 2) :=
  (twoDGround_hasDerivAt r θ).deriv

private theorem twoDGround_second_hasDerivAt (r θ : ℝ) :
    HasDerivAt (deriv (twoDGround r))
      (Real.exp (-(r * Real.cos θ) / 3) *
        (-(Real.sin θ) + r * Real.sin θ * Real.cos θ +
          r ^ 2 / 9 * (Real.sin θ) ^ 3)) θ := by
  have hfun : deriv (twoDGround r) =
      fun x : ℝ =>
        Real.exp (-(r * Real.cos x) / 3) *
          (Real.cos x + r / 3 * (Real.sin x) ^ 2) := by
    funext x
    exact twoDGround_deriv r x
  rw [hfun]
  have harg : HasDerivAt
      (fun x : ℝ => -(r * Real.cos x) / 3)
      (r * Real.sin θ / 3) θ := by
    convert (((Real.hasDerivAt_cos θ).const_mul r).neg).div_const 3 using 1
    ring
  have hinner : HasDerivAt
      (fun x : ℝ => Real.cos x + r / 3 * (Real.sin x) ^ 2)
      (-Real.sin θ + (2 * r / 3) * Real.sin θ * Real.cos θ) θ := by
    convert (Real.hasDerivAt_cos θ).add
      ((Real.hasDerivAt_sin θ).pow 2 |>.const_mul (r / 3)) using 1
    ring
  have hprod := harg.exp.mul hinner
  convert hprod using 1
  ring

private theorem twoDGround_operator (r θ : ℝ) :
    twoDOperatorValue r θ
        (deriv (twoDGround r) θ)
        (deriv (deriv (twoDGround r)) θ) -
      twoDGround r θ =
      (2 * r ^ 2 / 9) * (Real.sin θ) ^ 3 *
        Real.exp (-(r * Real.cos θ) / 3) := by
  rw [twoDGround_deriv,
    (twoDGround_second_hasDerivAt r θ).deriv]
  unfold twoDOperatorValue twoDGround
  ring

private theorem twoDLift_hasDerivAt (θ : ℝ) :
    HasDerivAt twoDLift (-2 * Real.sin θ * Real.cos θ) θ := by
  unfold twoDLift
  convert (Real.hasDerivAt_cos θ).pow 2 using 1
  ring

private theorem twoDLift_second_hasDerivAt (θ : ℝ) :
    HasDerivAt (deriv twoDLift)
      (2 * (Real.sin θ) ^ 2 - 2 * (Real.cos θ) ^ 2) θ := by
  have hfun : deriv twoDLift =
      fun x : ℝ => -2 * Real.sin x * Real.cos x := by
    funext x
    exact (twoDLift_hasDerivAt x).deriv
  rw [hfun]
  convert ((Real.hasDerivAt_sin θ).mul
    (Real.hasDerivAt_cos θ) |>.const_mul (-2)) using 1
  · funext x
    simp only [Pi.mul_apply]
    ring
  · ring_nf

private theorem twoDLift_operator (r θ : ℝ) :
    twoDOperatorValue r θ
        (deriv twoDLift θ)
        (deriv (deriv twoDLift) θ) -
      twoDLift θ =
      1 - (3 + 2 * r * Real.cos θ) * (Real.sin θ) ^ 2 := by
  rw [(twoDLift_hasDerivAt θ).deriv,
    (twoDLift_second_hasDerivAt θ).deriv]
  unfold twoDOperatorValue twoDLift
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- An explicit small endpoint lift keeps the positive ground-state
residual strictly positive.  The estimate needs only `0 ≤ x ≤ 1`,
`y ≤ 1`, and a lower bound on the exponential factor. -/
private theorem barrier_residual_algebra
    (r x y E E₀ : ℝ)
    (hr : 0 < r) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy1 : y ≤ 1) (hE : E₀ ≤ E) (hE0 : 0 < E₀) :
    0 <
      (2 * r ^ 2 / 9) * x ^ 3 * E +
        (E₀ * r ^ 2 / (100 * (3 + 2 * r) ^ 3)) *
          (1 - (3 + 2 * r * y) * x ^ 2) := by
  let K : ℝ := 3 + 2 * r
  let ε : ℝ := E₀ * r ^ 2 / (100 * K ^ 3)
  have hK : 0 < K := by dsimp [K]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hcoeff : 3 + 2 * r * y ≤ K := by
    dsimp [K]
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hy1)]
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hx2le : x ^ 2 ≤ 1 := by nlinarith
  have hG : 1 - K ≤ 1 - (3 + 2 * r * y) * x ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hcoeff hx2
    nlinarith [mul_le_mul_of_nonneg_left hx2le hK.le]
  change 0 <
    (2 * r ^ 2 / 9) * x ^ 3 * E +
      ε * (1 - (3 + 2 * r * y) * x ^ 2)
  by_cases hsmall : x ^ 2 ≤ 1 / (2 * K)
  · have hGsmall : 1 / 2 ≤ 1 - (3 + 2 * r * y) * x ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hcoeff hx2
      have hKsmall : K * x ^ 2 ≤ 1 / 2 := by
        have := mul_le_mul_of_nonneg_left hsmall hK.le
        field_simp at this
        linarith
      linarith
    have hEpos : 0 < E := lt_of_lt_of_le hE0 hE
    have hF : 0 ≤ (2 * r ^ 2 / 9) * x ^ 3 * E := by positivity
    have hGnonneg : 0 ≤ 1 - (3 + 2 * r * y) * x ^ 2 := by
      linarith
    nlinarith [mul_nonneg hε.le hGnonneg]
  · have hlarge : 1 / (2 * K) < x ^ 2 := lt_of_not_ge hsmall
    have hquad : 1 / (4 * K ^ 2) < (x ^ 2) ^ 2 := by
      have hhalf : 0 < 1 / (2 * K) := by positivity
      have hmul := mul_pos (sub_pos.mpr hlarge)
        (add_pos (lt_trans hhalf hlarge) hhalf)
      field_simp at hmul ⊢
      nlinarith
    have hx4 : (x ^ 2) ^ 2 ≤ x ^ 3 := by
      have hxx : x ^ 2 ≤ x := by nlinarith
      have hmul := mul_le_mul_of_nonneg_right hxx hx2
      nlinarith
    have hF :
        E₀ * r ^ 2 / (18 * K ^ 2) <
          (2 * r ^ 2 / 9) * x ^ 3 * E := by
      have hEpos : 0 < E := lt_of_lt_of_le hE0 hE
      have hq : 1 / (4 * K ^ 2) < x ^ 3 := lt_of_lt_of_le hquad hx4
      have hscale : 0 < (2 * r ^ 2 / 9) * E₀ := by positivity
      have hmul := mul_lt_mul_of_pos_left hq hscale
      have hEcmp := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤
        (2 * r ^ 2 / 9) * x ^ 3)
      dsimp [K] at *
      field_simp at hmul ⊢
      nlinarith
    have hEG : -(ε * K) ≤
        ε * (1 - (3 + 2 * r * y) * x ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hG hε.le]
    have hbound : ε * K <
        E₀ * r ^ 2 / (18 * K ^ 2) := by
      dsimp [ε]
      field_simp
      nlinarith [sq_pos_of_pos hK]
    linarith

def twoDBarrierEpsilon (r : ℝ) : ℝ :=
  Real.exp (-r / 3) * r ^ 2 /
    (100 * (3 + 2 * r) ^ 3)

private theorem twoDBarrier_deriv (r ε θ : ℝ) :
    deriv (twoDBarrier r ε) θ =
      deriv (twoDGround r) θ + ε * deriv twoDLift θ := by
  unfold twoDBarrier
  convert ((twoDGround_hasDerivAt r θ).add
    ((twoDLift_hasDerivAt θ).const_mul ε)).deriv using 1
  rw [twoDGround_deriv, (twoDLift_hasDerivAt θ).deriv]

private theorem twoDBarrier_second_deriv (r ε θ : ℝ) :
    deriv (deriv (twoDBarrier r ε)) θ =
      deriv (deriv (twoDGround r)) θ +
        ε * deriv (deriv twoDLift) θ := by
  have hfun : deriv (twoDBarrier r ε) =
      fun x : ℝ =>
        deriv (twoDGround r) x + ε * deriv twoDLift x := by
    funext x
    exact twoDBarrier_deriv r ε x
  rw [hfun]
  convert ((twoDGround_second_hasDerivAt r θ).add
    ((twoDLift_second_hasDerivAt θ).const_mul ε)).deriv using 1
  rw [(twoDGround_second_hasDerivAt r θ).deriv,
    (twoDLift_second_hasDerivAt θ).deriv]

private theorem twoDBarrier_operator_expansion (r ε θ : ℝ) :
    twoDOperatorValue r θ
        (deriv (twoDBarrier r ε) θ)
        (deriv (deriv (twoDBarrier r ε)) θ) -
      twoDBarrier r ε θ =
      (2 * r ^ 2 / 9) * (Real.sin θ) ^ 3 *
          Real.exp (-(r * Real.cos θ) / 3) +
        ε * (1 - (3 + 2 * r * Real.cos θ) *
          (Real.sin θ) ^ 2) := by
  rw [twoDBarrier_deriv, twoDBarrier_second_deriv]
  have hg := twoDGround_operator r θ
  have hv := twoDLift_operator r θ
  unfold twoDOperatorValue at hg hv ⊢
  unfold twoDBarrier
  linear_combination hg + ε * hv

/-- The explicit lift coefficient is strictly positive for every
positive physical field. -/
theorem twoDBarrierEpsilon_pos (r : ℝ) (hr : 0 < r) :
    0 < twoDBarrierEpsilon r := by
  unfold twoDBarrierEpsilon
  positivity

/-- An explicitly constructed smooth profile is strictly positive on
the closed physical angular interval. -/
theorem twoDBarrier_pos (r : ℝ) (hr : 0 < r)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    0 < twoDBarrier r (twoDBarrierEpsilon r) θ := by
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc hθ
  have hε := twoDBarrierEpsilon_pos r hr
  by_cases hsp : 0 < Real.sin θ
  · have hg : 0 < twoDGround r θ := by
      unfold twoDGround
      exact mul_pos hsp (Real.exp_pos _)
    have hv : 0 ≤ twoDBarrierEpsilon r * twoDLift θ := by
      exact mul_nonneg hε.le (by unfold twoDLift; positivity)
    unfold twoDBarrier
    linarith
  · have hs0 : Real.sin θ = 0 := le_antisymm (le_of_not_gt hsp) hsin
    have hc : (Real.cos θ) ^ 2 = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    simp [twoDBarrier, twoDGround, twoDLift, hs0, hc, hε]

/-- The original two-dimensional operator lies *strictly* above 1 on
the positive lifted profile.  This is an unconditional pointwise input
to a future weak-form Picone/spectral argument. -/
theorem twoDBarrier_strict_supersolution
    (r : ℝ) (hr : 0 < r)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    twoDBarrier r (twoDBarrierEpsilon r) θ <
      twoDOperatorValue r θ
        (deriv (twoDBarrier r (twoDBarrierEpsilon r)) θ)
        (deriv (deriv (twoDBarrier r (twoDBarrierEpsilon r))) θ) := by
  have hsin0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc hθ
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hE : Real.exp (-r / 3) ≤
      Real.exp (-(r * Real.cos θ) / 3) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hcos1)]
  have hres := barrier_residual_algebra r
    (Real.sin θ) (Real.cos θ)
    (Real.exp (-(r * Real.cos θ) / 3))
    (Real.exp (-r / 3))
    hr hsin0 hsin1 hcos1 hE (Real.exp_pos _)
  have hidentity :=
    twoDBarrier_operator_expansion r (twoDBarrierEpsilon r) θ
  unfold twoDBarrierEpsilon at hidentity ⊢
  linarith

end

end DFL.GCI
