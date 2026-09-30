import Mathlib

/-!
# A Picone identity for absolutely continuous Dirichlet representatives

This is the weak one-dimensional algebraic bridge needed for the original
angular GCI problem. The factor `A` will later be `φ'/φ` for a positive
smooth supersolution; this file assumes only the absolute continuity of
`p*A`, making the integration by parts valid for an `H¹₀` representative.
-/

namespace DFL.Probability

open MeasureTheory
open scoped Interval

noncomputable section

/-- The exact integrated square completion for an absolutely continuous
Dirichlet representative. All three quadratic integrability conditions are
explicit; no hidden smoothness of `u` is assumed. -/
theorem picone_integral_identity_ac
    {a b : ℝ} (u p A : ℝ → ℝ)
    (hu : AbsolutelyContinuousOnInterval u a b)
    (hf : AbsolutelyContinuousOnInterval (fun x => p x * A x) a b)
    (hua : u a = 0) (hub : u b = 0)
    (hE : IntervalIntegrable (fun x => p x * (deriv u x) ^ 2)
      volume a b)
    (hQ : IntervalIntegrable
      (fun x => p x * (deriv u x - A x * u x) ^ 2)
      volume a b)
    (hV : IntervalIntegrable
      (fun x =>
        (-(deriv (fun y => p y * A y) x) - p x * A x ^ 2) * u x ^ 2)
      volume a b) :
    (∫ x in a..b, p x * (deriv u x) ^ 2) =
      (∫ x in a..b, p x * (deriv u x - A x * u x) ^ 2) +
        ∫ x in a..b,
          (-(deriv (fun y => p y * A y) x) - p x * A x ^ 2) * u x ^ 2 := by
  let f : ℝ → ℝ := fun x => p x * A x
  let E : ℝ → ℝ := fun x => p x * (deriv u x) ^ 2
  let Q : ℝ → ℝ := fun x => p x * (deriv u x - A x * u x) ^ 2
  let V : ℝ → ℝ := fun x => (-deriv f x - p x * A x ^ 2) * u x ^ 2
  have hu2 : AbsolutelyContinuousOnInterval (fun x => u x ^ 2) a b := by
    simpa only [pow_two] using hu.mul hu
  have hprod : AbsolutelyContinuousOnInterval (fun x => f x * u x ^ 2) a b :=
    hf.mul hu2
  have hder : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b →
      deriv (fun y => f y * u y ^ 2) x = E x - Q x - V x := by
    filter_upwards [hf.ae_differentiableAt, hu.ae_differentiableAt]
      with x hfd hud hx
    have hx' : x ∈ Set.uIcc a b := by
      grind [Set.uIcc, Set.uIoc]
    have hF := (hfd hx').hasDerivAt
    have hU := (hud hx').hasDerivAt
    have hU2 : HasDerivAt (fun y => u y ^ 2)
        (2 * u x * deriv u x) x := by
      convert hU.pow 2 using 1
      ring
    have hp := hF.mul hU2
    have hpoint : deriv (fun y => f y * u y ^ 2) x =
        deriv f x * u x ^ 2 + f x * (2 * u x * deriv u x) := by
      convert hp.deriv using 1
    rw [hpoint]
    dsimp [E, Q, V, f]
    ring
  have hmatch :
      (∫ x in a..b, deriv (fun y => f y * u y ^ 2) x) =
        ∫ x in a..b, E x - Q x - V x := by
    apply intervalIntegral.integral_congr_ae
    exact hder
  have hboundary :
      (∫ x in a..b, deriv (fun y => f y * u y ^ 2) x) = 0 := by
    rw [hprod.integral_deriv_eq_sub, hua, hub]
    ring
  have hE' : IntervalIntegrable E volume a b := hE
  have hQ' : IntervalIntegrable Q volume a b := hQ
  have hV' : IntervalIntegrable V volume a b := hV
  rw [intervalIntegral.integral_sub (hE'.sub hQ') hV',
    intervalIntegral.integral_sub hE' hQ'] at hmatch
  rw [hboundary] at hmatch
  change (∫ x in a..b, E x) =
    (∫ x in a..b, Q x) + ∫ x in a..b, V x
  linarith

/-- A strictly stronger comparison than the baseline potential follows
whenever the Picone remainder is continuous, nonnegative in the interval,
and positive at one point.  In the GCI application the barrier makes the
remainder positive wherever the weak solution is nonzero. -/
theorem picone_strict_energy_ac
    {a b : ℝ} (u p A : ℝ → ℝ) (hab : a < b)
    (hu : AbsolutelyContinuousOnInterval u a b)
    (hf : AbsolutelyContinuousOnInterval (fun x => p x * A x) a b)
    (hua : u a = 0) (hub : u b = 0)
    (hp : ∀ x ∈ Set.Icc a b, 0 ≤ p x)
    (hE : IntervalIntegrable (fun x => p x * (deriv u x) ^ 2)
      volume a b)
    (hQ : IntervalIntegrable
      (fun x => p x * (deriv u x - A x * u x) ^ 2)
      volume a b)
    (hV : IntervalIntegrable
      (fun x =>
        (-(deriv (fun y => p y * A y) x) - p x * A x ^ 2) * u x ^ 2)
      volume a b)
    (hL2 : IntervalIntegrable (fun x => p x * u x ^ 2) volume a b)
    (hR : IntervalIntegrable
      (fun x =>
        (-(deriv (fun y => p y * A y) x) - p x * A x ^ 2 - p x) * u x ^ 2)
      volume a b)
    (hRcont : ContinuousOn
      (fun x =>
        (-(deriv (fun y => p y * A y) x) - p x * A x ^ 2 - p x) * u x ^ 2)
      (Set.Icc a b))
    (hRnonneg : ∀ x ∈ Set.Ioc a b,
      0 ≤ (-(deriv (fun y => p y * A y) x) - p x * A x ^ 2 - p x) * u x ^ 2)
    (hRpos : ∃ x ∈ Set.Icc a b,
      0 < (-(deriv (fun y => p y * A y) x) - p x * A x ^ 2 - p x) * u x ^ 2) :
    (∫ x in a..b, p x * u x ^ 2) <
      ∫ x in a..b, p x * (deriv u x) ^ 2 := by
  have hidentity := picone_integral_identity_ac u p A hu hf hua hub hE hQ hV
  have hQnonneg :
      0 ≤ ∫ x in a..b, p x * (deriv u x - A x * u x) ^ 2 := by
    apply intervalIntegral.integral_nonneg hab.le
    intro x hx
    exact mul_nonneg (hp x hx) (sq_nonneg _)
  have hRstrict :
      0 < ∫ x in a..b,
        (-(deriv (fun y => p y * A y) x) - p x * A x ^ 2 - p x) * u x ^ 2 :=
    intervalIntegral.integral_pos hab hRcont hRnonneg hRpos
  have hsplit :
      (∫ x in a..b,
        (-(deriv (fun y => p y * A y) x) - p x * A x ^ 2) * u x ^ 2) =
        (∫ x in a..b, p x * u x ^ 2) +
          ∫ x in a..b,
            (-(deriv (fun y => p y * A y) x) - p x * A x ^ 2 - p x) *
              u x ^ 2 := by
    rw [← intervalIntegral.integral_add hL2 hR]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hsplit] at hidentity
  linarith

end

end DFL.Probability
