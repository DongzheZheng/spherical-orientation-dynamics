import DFL.Hysteresis.MomentRecurrence
import DFL.Hysteresis.MarginalDerivative

/-!
# The small-field slope of the original DFL orientation mean

The zero-field second moment is established by integration by parts on the
original spherical marginal.  In dimension two the differentiated primitive
has an endpoint singularity, so the proof uses interval integrability and an
interior derivative rather than endpoint differentiability.
-/

namespace DFL

open MeasureTheory Set Filter
open scoped Interval Topology

noncomputable section

private def zeroFieldPrimitive (n : ℕ) (t : ℝ) : ℝ :=
  t * (1 - t ^ 2) ^ (((n : ℝ) - 1) / 2)

private def zeroFieldIntegrand (n : ℕ) (t : ℝ) : ℝ :=
  marginalWeight n 0 t - (n : ℝ) * (t ^ 2 * marginalWeight n 0 t)

private theorem zeroFieldPrimitive_continuousOn (n : ℕ) (hn : 2 ≤ n) :
    ContinuousOn (zeroFieldPrimitive n) (Icc (-1 : ℝ) 1) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hβ : 0 ≤ (((n : ℝ) - 1) / 2) := by linarith
  have hb : ContinuousOn (fun t : ℝ => 1 - t ^ 2) (Icc (-1 : ℝ) 1) := by
    fun_prop
  have hp : ContinuousOn
      (fun t : ℝ => (1 - t ^ 2) ^ (((n : ℝ) - 1) / 2))
      (Icc (-1 : ℝ) 1) :=
    hb.rpow_const (fun _ _ => Or.inr hβ)
  have ht : ContinuousOn (fun t : ℝ => t) (Icc (-1 : ℝ) 1) := by fun_prop
  simpa only [zeroFieldPrimitive] using ht.mul hp

private theorem zeroFieldPrimitive_hasDerivAt (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (zeroFieldPrimitive n) (zeroFieldIntegrand n t) t := by
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
  have hbase : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * t) t := by
    convert (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2) using 1
    norm_num
  have hpow : HasDerivAt
      (fun x : ℝ => (1 - x ^ 2) ^ β)
      ((-2 * t) * β * b ^ (β - 1)) t := by
    simpa only [b] using hbase.rpow_const (Or.inl hbnz)
  have hproduct := (hasDerivAt_id t).mul hpow
  convert hproduct using 1
  simp only [zeroFieldIntegrand, marginalWeight, zero_mul, Real.exp_zero, one_mul]
  rw [show (1 - t ^ 2) = b from rfl, hβα, hβpow]
  dsimp [b, α, β]
  ring

private theorem zeroFieldIntegrand_intervalIntegrable (n : ℕ) (hn : 2 ≤ n) :
    IntervalIntegrable (zeroFieldIntegrand n) volume (-1 : ℝ) 1 := by
  have hZ := marginalWeight_intervalIntegrable n hn 0
  have hM₂ := secondMoment_intervalIntegrable n hn 0
  exact hZ.sub (hM₂.const_mul (n : ℝ))

/-- The exact zero-field isotropic second-moment identity for the original
DFL marginal, valid also for the singular endpoint case `n = 2`. -/
theorem zero_field_second_moment (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * secondMoment n 0 = partition n 0 := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (-1 : ℝ) ≤ 1)
    (zeroFieldPrimitive_continuousOn n hn)
    (fun t ht => zeroFieldPrimitive_hasDerivAt n ht)
    (zeroFieldIntegrand_intervalIntegrable n hn)
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hβ : (((n : ℝ) - 1) / 2) ≠ 0 := by linarith
  have hend : zeroFieldPrimitive n 1 - zeroFieldPrimitive n (-1) = 0 := by
    simp [zeroFieldPrimitive, Real.zero_rpow hβ]
  rw [hend] at hFTC
  have hZ := marginalWeight_intervalIntegrable n hn 0
  have hM₂ := secondMoment_intervalIntegrable n hn 0
  simp only [zeroFieldIntegrand] at hFTC
  rw [intervalIntegral.integral_sub hZ (hM₂.const_mul (n : ℝ)),
    intervalIntegral.integral_const_mul] at hFTC
  change partition n 0 - (n : ℝ) * secondMoment n 0 = 0 at hFTC
  linarith

/-- Oddness of the zero-field first moment, obtained from the original
all-field recurrence rather than postulated as a symmetry axiom. -/
theorem firstMoment_zero (n : ℕ) (hn : 2 ≤ n) : firstMoment n 0 = 0 := by
  have hrec := moment_recurrence n hn 0
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp only [zero_mul] at hrec
  nlinarith

theorem orientationMean_zero (n : ℕ) (hn : 2 ≤ n) : orientationMean n 0 = 0 := by
  unfold orientationMean
  rw [firstMoment_zero n hn]
  simp

/-- Susceptibility at zero field for the actual spherical orientation mean. -/
theorem orientationMean_deriv_zero (n : ℕ) (hn : 2 ≤ n) :
    deriv (orientationMean n) 0 = 1 / (n : ℝ) := by
  have hZpos := partition_pos n hn 0
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [orientationMean_deriv n hn 0, orientationMean_zero n hn]
  have hM := zero_field_second_moment n hn
  field_simp
  nlinarith

/-- The original DFL mean has the small-field slope `1/n`, using its defining
integrals and no assumed limiting susceptibility. -/
theorem orientationMean_div_tendsto_zero_right (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun r : ℝ => orientationMean n r / r)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / (n : ℝ))) := by
  have hder : HasDerivAt (orientationMean n) (1 / (n : ℝ)) 0 := by
    convert (orientationMean_differentiableAt n hn 0).hasDerivAt using 1
    exact (orientationMean_deriv_zero n hn).symm
  have hlim := hder.tendsto_slope_zero_right
  simpa only [zero_add, orientationMean_zero n hn, sub_zero, smul_eq_mul,
    inv_mul_eq_div] using hlim

private theorem inverseAlignment_hasDerivAt_zero :
    HasDerivAt inverseAlignment 1 0 := by
  have hlin : HasDerivAt (fun x : ℝ => 1 + 4 * x) 4 0 := by
    convert (hasDerivAt_const 0 (1 : ℝ)).add
      ((hasDerivAt_id 0).const_mul 4) using 1
    ring
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (1 + 4 * x))
      (4 / (2 * Real.sqrt (1 + 4 * (0 : ℝ)))) 0 :=
    hlin.sqrt (by norm_num)
  have hformula : HasDerivAt inverseAlignment
      ((4 / (2 * Real.sqrt (1 + 4 * (0 : ℝ)))) / 2) 0 := by
    convert (hsqrt.sub_const 1).div_const 2 using 1
  convert hformula using 1
  norm_num

private theorem inverseAlignment_div_tendsto_zero_right :
    Tendsto (fun r : ℝ => inverseAlignment r / r)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
  have hlim := inverseAlignment_hasDerivAt_zero.tendsto_slope_zero_right
  have hzero : inverseAlignment 0 = 0 := by simp [inverseAlignment]
  simpa only [zero_add, hzero, sub_zero, smul_eq_mul, inv_mul_eq_div] using hlim

/-- The original density endpoint clause in `DFL.Targets`, derived from the
feedback law and the proved small-field slope of its spherical mean. -/
theorem endpointAtZero (n : ℕ) (hn : 2 ≤ n) : EndpointAtZero n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hclim := orientationMean_div_tendsto_zero_right n hn
  have hjlim := inverseAlignment_div_tendsto_zero_right
  have hquot : Tendsto
      (fun r : ℝ => (inverseAlignment r / r) / (orientationMean n r / r))
      (𝓝[>] (0 : ℝ)) (𝓝 ((n : ℝ))) := by
    convert hjlim.div hclim (by exact one_div_ne_zero (ne_of_gt hnR)) using 1
    field_simp
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrpos : 0 < r := hr
  have hczero : orientationMean n r ≠ 0 := ne_of_gt (orientationMean_pos n hn hrpos)
  have hrzero : r ≠ 0 := ne_of_gt hrpos
  dsimp [equilibriumDensity]
  field_simp

end

end DFL
