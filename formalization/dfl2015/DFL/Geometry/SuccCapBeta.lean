import DFL.Geometry.SuccCapReal

/-!
# Scalar beta-tail identity in successor dimensions

This file isolates the remaining integration-by-parts identity from the
genuine geometric Fubini reduction.
-/

namespace DFL.Geometry

open MeasureTheory
open scoped Interval

noncomputable section

def betaPower (k : ℕ) (s : ℝ) : ℝ :=
  (Real.sqrt (1 - s ^ 2)) ^ k

private def betaPrimitive (k : ℕ) (s : ℝ) : ℝ :=
  s * betaPower (k + 2) s

private def betaDerivative (k : ℕ) (s : ℝ) : ℝ :=
  ((k + 3 : ℕ) : ℝ) * betaPower (k + 2) s -
    ((k + 2 : ℕ) : ℝ) * betaPower k s

private theorem betaPrimitive_hasDerivAt (k : ℕ) (s : ℝ)
    (hs : 0 < s) (hs1 : s < 1) :
    HasDerivAt (betaPrimitive k) (betaDerivative k s) s := by
  have hbase : 0 < 1 - s ^ 2 := by nlinarith
  have hu : 0 < Real.sqrt (1 - s ^ 2) := Real.sqrt_pos.2 hbase
  have hpoly : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * s) s := by
    convert (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).pow 2) using 1;
      simp [mul_comm]
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x ^ 2))
      ((1 / (2 * Real.sqrt (1 - s ^ 2))) * (-2 * s)) s :=
    (Real.hasDerivAt_sqrt hbase.ne').comp s hpoly
  have hder := (hasDerivAt_id s).mul (hsqrt.pow (k + 2))
  convert hder using 1
  · dsimp [betaDerivative, betaPower]
    simp only [one_mul]
    let u : ℝ := Real.sqrt (1 - s ^ 2)
    have hne : u ≠ 0 := hu.ne'
    have hsqr : u ^ 2 = 1 - s ^ 2 := Real.sq_sqrt hbase.le
    change ((k + 3 : ℕ) : ℝ) * u ^ (k + 2) -
        ((k + 2 : ℕ) : ℝ) * u ^ k =
      u ^ (k + 2) + s *
        (((k + 2 : ℕ) : ℝ) * u ^ (k + 1) *
          (1 / (2 * u) * (-2 * s)))
    rw [pow_add u k 2, pow_add u k 1]
    simp only [pow_one]
    field_simp
    rw [show u ^ 2 = 1 - s ^ 2 from hsqr]
    push_cast
    ring

/-- The one-dimensional reduction-of-order identity behind all beta tails
with exponent at least zero. It includes every remaining physical sphere
dimension n ≥ 4 after setting m = k+2. -/
theorem beta_tail_recursion (k : ℕ) (t : ℝ)
    (ht : 0 < t) (ht1 : t < 1) :
    t * betaPower (k + 2) t +
      ((k + 3 : ℕ) : ℝ) * (∫ s in t..1, betaPower (k + 2) s) =
        ((k + 2 : ℕ) : ℝ) * (∫ s in t..1, betaPower k s) := by
  have hcprim : Continuous (betaPrimitive k) := by
    unfold betaPrimitive betaPower
    fun_prop
  have hcderiv : Continuous (betaDerivative k) := by
    unfold betaDerivative betaPower
    fun_prop
  have hdiff : ∀ s ∈ Set.Ioo t 1,
      HasDerivAt (betaPrimitive k) (betaDerivative k s) s := by
    intro s hs
    exact betaPrimitive_hasDerivAt k s (ht.trans hs.1) hs.2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    ht1.le (hcprim.continuousOn) hdiff (hcderiv.intervalIntegrable t 1)
  have hleft : betaPrimitive k 1 = 0 := by
    simp [betaPrimitive, betaPower]
  rw [hleft, zero_sub] at hFTC
  have hcplus : Continuous (betaPower (k + 2)) := by
    unfold betaPower
    fun_prop
  have hcbase : Continuous (betaPower k) := by
    unfold betaPower
    fun_prop
  simp only [betaDerivative] at hFTC
  rw [intervalIntegral.integral_sub
      ((hcplus.const_mul _).intervalIntegrable t 1)
      ((hcbase.const_mul _).intervalIntegrable t 1),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hFTC
  dsimp [betaPrimitive] at hFTC
  linarith

/-- Positive upper-tail mass of the actual original sphere in every
ambient dimension `k+3≥3`, expressed as the beta integral with the
correct Gamma-normalized transverse area factor. -/
theorem coordinateLaw_succ_Ioi_beta_real (k : ℕ) (t : ℝ)
    (ht : 0 < t) (ht1 : t < 1) :
    (coordinateLaw (k + 3) (by omega)).real (Set.Ioi t) =
      ((k + 2 : ℕ) : ℝ) * gammaBallConst (k + 2) *
        (∫ s in t..1, betaPower k s) := by
  have hcap := coordinateLaw_succ_Ioi_gamma (k + 2)
    (by omega : 0 < k + 2) t ht ht1
  have hcoef : (((k + 2 : ℕ) : ENNReal) + 1).toReal =
      ((k + 3 : ℕ) : ℝ) := by
    have hcast : (((k + 2 : ℕ) : ENNReal) + 1) =
        ((k + 3 : ℕ) : ENNReal) := by norm_cast
    rw [hcast, ENNReal.toReal_natCast]
  change ((coordinateLaw (k + 3) (by omega)) (Set.Ioi t)).toReal = _
  rw [hcap, ENNReal.toReal_mul, hcoef,
    scalarCapKernel_lintegral_real (k + 2) t ht ht1,
    smallGammaSlice_integral (k + 2) t ht]
  have hlarge : (∫ s in t..1, largeGammaSlice (k + 2) s) =
      (∫ s in t..1, betaPower (k + 2) s) * gammaBallConst (k + 2) := by
    simp only [largeGammaSlice, betaPower]
    rw [intervalIntegral.integral_mul_const]
  rw [hlarge]
  have hden : ((k + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  have hrec := beta_tail_recursion k t ht ht1
  calc
    _ = gammaBallConst (k + 2) *
          (t * betaPower (k + 2) t +
            ((k + 3 : ℕ) : ℝ) * (∫ s in t..1, betaPower (k + 2) s)) := by
      dsimp [betaPower]
      field_simp [hden]
      push_cast
      ring
    _ = gammaBallConst (k + 2) *
          (((k + 2 : ℕ) : ℝ) * (∫ s in t..1, betaPower k s)) := by
      rw [hrec]
    _ = _ := by ring

end

end DFL.Geometry
