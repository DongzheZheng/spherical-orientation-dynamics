import DFL.Hysteresis.MomentDerivative

/-!
# Moment recurrence from the original DFL marginal

The proof differentiates `exp (r t) * (1 - t²)^((n - 1)/2)` on the open
interval and applies the fundamental theorem with an interval-integrable
derivative.  This covers `n = 2`: its derivative has an integrable endpoint
singularity, while the antiderivative itself vanishes at both endpoints.
No Riccati relation is assumed.
-/

namespace DFL

open MeasureTheory Set
open scoped Interval

noncomputable section

private def boundaryPrimitive (n : ℕ) (r t : ℝ) : ℝ :=
  Real.exp (r * t) * (1 - t ^ 2) ^ (((n : ℝ) - 1) / 2)

private def recurrenceIntegrand (n : ℕ) (r t : ℝ) : ℝ :=
  r * (marginalWeight n r t - t ^ 2 * marginalWeight n r t) -
    ((n : ℝ) - 1) * (t * marginalWeight n r t)

private theorem boundaryPrimitive_continuousOn (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    ContinuousOn (boundaryPrimitive n r) (Icc (-1 : ℝ) 1) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hβ : 0 ≤ (((n : ℝ) - 1) / 2) := by linarith
  have hb : ContinuousOn (fun t : ℝ => 1 - t ^ 2) (Icc (-1 : ℝ) 1) := by
    fun_prop
  have hp : ContinuousOn
      (fun t : ℝ => (1 - t ^ 2) ^ (((n : ℝ) - 1) / 2))
      (Icc (-1 : ℝ) 1) :=
    hb.rpow_const (fun _ _ => Or.inr hβ)
  have he : ContinuousOn (fun t : ℝ => Real.exp (r * t))
      (Icc (-1 : ℝ) 1) := by fun_prop
  simpa only [boundaryPrimitive] using he.mul hp

private theorem boundaryPrimitive_hasDerivAt (n : ℕ) (r : ℝ) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (boundaryPrimitive n r) (recurrenceIntegrand n r t) t := by
  let b : ℝ := 1 - t ^ 2
  let α : ℝ := ((n : ℝ) - 3) / 2
  let β : ℝ := ((n : ℝ) - 1) / 2
  have hbpos : 0 < b := by
    dsimp [b]
    have hprod : 0 < (1 - t) * (1 + t) :=
      mul_pos (by linarith [ht.2]) (by linarith [ht.1])
    nlinarith [hprod]
  have hbnz : b ≠ 0 := ne_of_gt hbpos
  have hβα : β - 1 = α := by dsimp [β, α]; ring
  have hβpow : b ^ β = b * b ^ α := by
    have hβeq : β = 1 + α := by dsimp [β, α]; ring
    rw [hβeq, Real.rpow_add hbpos]
    simp
  have hlinear : HasDerivAt (fun x : ℝ => r * x) r t := by
    convert (hasDerivAt_id t).const_mul r using 1
    ring
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (r * x))
      (Real.exp (r * t) * r) t := hlinear.exp
  have hbase : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * t) t := by
    convert (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2) using 1
    norm_num
  have hpow : HasDerivAt
      (fun x : ℝ => (1 - x ^ 2) ^ β)
      ((-2 * t) * β * b ^ (β - 1)) t := by
    simpa only [b] using hbase.rpow_const (Or.inl hbnz)
  have hproduct := hexp.mul hpow
  convert hproduct using 1
  simp only [recurrenceIntegrand, marginalWeight]
  rw [show (1 - t ^ 2) = b from rfl, hβα, hβpow]
  dsimp [b, α, β]
  ring

private theorem recurrenceIntegrand_intervalIntegrable (n : ℕ)
    (hn : 2 ≤ n) (r : ℝ) :
    IntervalIntegrable (recurrenceIntegrand n r) volume (-1 : ℝ) 1 := by
  have hZ := marginalWeight_intervalIntegrable n hn r
  have hM₂ := secondMoment_intervalIntegrable n hn r
  have hM₁ := firstMoment_intervalIntegrable n hn r
  exact (hZ.sub hM₂).const_mul r |>.sub (hM₁.const_mul ((n : ℝ) - 1))

/-- Integration by parts for the *same* original marginal in `DFL.Targets`.
The interval FTC uses only an interior derivative and an integrable derivative;
it does not assume differentiability of the primitive at `t = ±1`. -/
theorem moment_recurrence (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    r * (partition n r - secondMoment n r) =
      ((n : ℝ) - 1) * firstMoment n r := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (-1 : ℝ) ≤ 1)
    (boundaryPrimitive_continuousOn n hn r)
    (fun t ht => boundaryPrimitive_hasDerivAt n r ht)
    (recurrenceIntegrand_intervalIntegrable n hn r)
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hβ : (((n : ℝ) - 1) / 2) ≠ 0 := by linarith
  have hend : boundaryPrimitive n r 1 - boundaryPrimitive n r (-1) = 0 := by
    simp [boundaryPrimitive, Real.zero_rpow hβ]
  rw [hend] at hFTC
  have hZ := marginalWeight_intervalIntegrable n hn r
  have hM₂ := secondMoment_intervalIntegrable n hn r
  have hM₁ := firstMoment_intervalIntegrable n hn r
  simp only [recurrenceIntegrand] at hFTC
  rw [intervalIntegral.integral_sub
    ((hZ.sub hM₂).const_mul r) (hM₁.const_mul ((n : ℝ) - 1)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hZ hM₂] at hFTC
  change r * (partition n r - secondMoment n r) -
    ((n : ℝ) - 1) * firstMoment n r = 0 at hFTC
  linarith

/-- The paper's Riccati identity for the original mean follows from the
proved moment recurrence once the two parameter-differentiation identities
for the same marginal are supplied.  Those identities remain explicit inputs. -/
theorem orientationMean_riccati_of_moment_derivs
    (n : ℕ) (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r)
    (hZ : HasDerivAt (partition n) (firstMoment n r) r)
    (hM : HasDerivAt (firstMoment n) (secondMoment n r) r) :
    deriv (orientationMean n) r =
      1 - ((n : ℝ) - 1) * orientationMean n r / r -
        (orientationMean n r) ^ 2 := by
  have hZpos := partition_pos n hn r
  have hZ0 : partition n r ≠ 0 := ne_of_gt hZpos
  have hrec := moment_recurrence n hn r
  rw [orientationMean_deriv_of_moment_derivs n r hZ hM hZ0]
  unfold orientationMean
  field_simp
  nlinarith [hrec]

end

end DFL
