import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import Mathlib.Analysis.Fourier.AddCircle

/-! The actual periodic derivative of a smooth function on the circle.
Fourier completeness and integration by parts derive the positive-frequency
lower bound; no spectral bound is an input. -/
noncomputable section
open Bundle Manifold MeasureTheory Set Complex AddCircle
open scoped Manifold Topology ContDiff Real BigOperators

namespace DFLCircleFourier

abbrev SmoothCircleComplex := C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); 𝓘(ℝ, ℂ), ℂ⟯

def parameterDerivative (F : SmoothCircleComplex) : SmoothCircleComplex :=
  ⟨fun z => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) F z (AddCircle.parameterTangent z),
    AddCircle.contMDiff_mfderiv_parameterTangent F.contMDiff (by simp) le_rfl⟩

theorem parameterDerivative_coe (F : SmoothCircleComplex) (t : ℝ) :
    parameterDerivative F (t : AddCircle (1 : ℝ)) =
      deriv (fun s : ℝ => F (s : AddCircle (1 : ℝ))) t :=
  (AddCircle.deriv_comp_coe (F.contMDiff.mdifferentiableAt (by simp))).symm

private theorem hasDerivAt_comp_coe (F : SmoothCircleComplex) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (s : AddCircle (1 : ℝ)))
      (parameterDerivative F (t : AddCircle (1 : ℝ))) t := by
  have hs := (F.contMDiff.comp AddCircle.contMDiff_coe).contDiff
  rw [parameterDerivative_coe]
  exact (hs.differentiable (by simp)).differentiableAt.hasDerivAt

private theorem fourierCoeffOn_unit (F : AddCircle (1 : ℝ) → ℂ) (n : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun t : ℝ => F (t : AddCircle (1 : ℝ))) n = fourierCoeff F n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral F n 0]
  simp

/-- Genuine integration by parts for every nonzero integer frequency. -/
theorem fourierCoeff_parameterDerivative (F : SmoothCircleComplex)
    (n : ℤ) (hn : n ≠ 0) :
    fourierCoeff (parameterDerivative F) n =
      (2 * Real.pi * Complex.I * (n : ℂ)) * fourierCoeff F n := by
  have hi := fourierCoeffOn_of_hasDerivAt (by norm_num : (0 : ℝ) < 1) hn
    (fun t _ => hasDerivAt_comp_coe F t)
    (((parameterDerivative F).contMDiff.continuous.comp
      (AddCircle.continuous_mk' 1)).intervalIntegrable 0 1)
  rw [fourierCoeffOn_unit, fourierCoeffOn_unit] at hi
  have hone : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 := AddCircle.coe_period 1
  simp only [hone, AddCircle.coe_zero, sub_self, mul_zero, one_mul, sub_zero, zero_sub,
    Complex.ofReal_zero, Complex.ofReal_one] at hi
  have hd : (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero, hn]
  have hm := congrArg (fun z : ℂ => (-2 * Real.pi * Complex.I * (n : ℂ)) * z) hi
  field_simp [hd] at hm
  linear_combination hm

/-- The zero-frequency coefficient of the true periodic derivative is zero. -/
theorem fourierCoeff_parameterDerivative_zero (F : SmoothCircleComplex) :
    fourierCoeff (parameterDerivative F) 0 = 0 := by
  rw [fourierCoeff_eq_intervalIntegral (parameterDerivative F) 0 0]
  simp only [neg_zero, fourier_zero, one_smul, zero_add, one_div, inv_one]
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_comp_coe F t)
    (((parameterDerivative F).contMDiff.continuous.comp
      (AddCircle.continuous_mk' 1)).intervalIntegrable 0 1)
  have hone : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 := AddCircle.coe_period 1
  simpa only [hone, AddCircle.coe_zero, sub_self, one_smul] using hint

/-- Fourier completeness detects a nonzero continuous function. -/
theorem exists_nonzero_fourierCoeff (F : C(AddCircle (1 : ℝ), ℂ)) (hF : F ≠ 0) :
    ∃ n : ℤ, fourierCoeff F n ≠ 0 := by
  by_contra hn
  push Not at hn
  have hz : ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ F = 0 := by
    apply fourierBasis.repr.injective
    ext n
    rw [fourierBasis_repr, fourierCoeff_toLp, hn]
    simp
  apply hF
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) haarAddCircle
  simpa using hz

/-- A genuine smooth periodic eigenfunction has a nonzero integer mode.
Its frequency identity yields the sharp positive eigenvalue lower bound. -/
theorem periodic_eigenvalue_ge_one
    (F : SmoothCircleComplex) (lam : ℝ) (hlam : 0 < lam)
    (hF : ∃ z, F z ≠ 0)
    (heig : ∀ z, parameterDerivative (parameterDerivative F) z =
      -((2 * Real.pi)^2 * lam : ℝ) * F z) :
    1 ≤ lam := by
  let FC : C(AddCircle (1 : ℝ), ℂ) := ⟨F, F.contMDiff.continuous⟩
  have hFC : FC ≠ 0 := by
    intro he
    obtain ⟨z, hz⟩ := hF
    apply hz
    exact congrArg (fun G : C(AddCircle (1 : ℝ), ℂ) => G z) he
  obtain ⟨n, hn⟩ := exists_nonzero_fourierCoeff FC hFC
  have hcoef : fourierCoeff (parameterDerivative (parameterDerivative F)) n =
      -((2 * Real.pi)^2 * lam : ℝ) * fourierCoeff F n := by
    have he : (parameterDerivative (parameterDerivative F) : AddCircle (1 : ℝ) → ℂ) =
        fun z => (-((2 * Real.pi)^2 * lam : ℝ) : ℂ) * F z := funext heig
    rw [he, fourierCoeff.const_mul]
  have hn0 : n ≠ 0 := by
    intro hzero
    subst n
    rw [fourierCoeff_parameterDerivative_zero] at hcoef
    have hc : (-((2 * Real.pi)^2 * lam : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (neg_ne_zero.mpr (mul_ne_zero
        (ne_of_gt (sq_pos_of_pos (by positivity : 0 < 2 * Real.pi))) (ne_of_gt hlam)))
    exact hn ((mul_eq_zero.mp hcoef.symm).resolve_left hc)
  rw [fourierCoeff_parameterDerivative _ n hn0,
    fourierCoeff_parameterDerivative _ n hn0] at hcoef
  have hc : fourierCoeff F n ≠ 0 := hn
  have heq : (2 * Real.pi * Complex.I * (n : ℂ)) ^ 2 =
      (-((2 * Real.pi)^2 * lam : ℝ) : ℂ) := by
    apply mul_right_cancel₀ hc
    simpa only [pow_two, mul_assoc] using hcoef
  have hre := congrArg Complex.re heq
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] at hre
  have hs : 0 < (2 * Real.pi)^2 := sq_pos_of_pos (by positivity)
  have hn1 : (1 : ℝ) ≤ (n : ℝ)^2 := by
    have ha : 1 ≤ n.natAbs := by
      have hp := Int.natAbs_pos.mpr hn0
      omega
    have haR : (1 : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast ha
    have hb : |(n : ℝ)| = (n.natAbs : ℝ) := by simp
    nlinarith [sq_abs (n : ℝ)]
  nlinarith

end DFLCircleFourier
