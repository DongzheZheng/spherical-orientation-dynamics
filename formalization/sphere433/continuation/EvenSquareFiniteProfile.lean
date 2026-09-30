import continuation.EvenSquareProfile
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-! The same Hadamard division and Taylor extension mechanism at every
finite order. Integrating the regularized radial derivative adds one
ordinary derivative and retains the original squared-radius identity. -/
noncomputable section
set_option maxHeartbeats 800000
open Set Filter Function MeasureTheory
open scoped Topology ContDiff
namespace DFLSphere
open DifferentialGeometry.Analysis.Calculus

private theorem even_deriv_neg_finite (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (x : ℝ) : deriv f (-x) = -deriv f x := by
  have hcomp := ((hf.differentiable (by simp) (-x)).hasDerivAt).comp x
    (hasDerivAt_id x).neg
  have heq : (fun y => f (-y)) = f := funext he
  change HasDerivAt (fun y => f (-y)) (deriv f (-x)*(-1)) x at hcomp
  rw [heq] at hcomp
  have hd := hcomp.deriv
  linarith

/-- The true Hadamard radial-square derivative pays the vanishing radial
factor at the pole; this is an identity of the actual original f. -/
theorem even_deriv_square_factor (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (x : ℝ) : deriv f x = 2*x*radialSquareDerivative f x := by
  have h0 : deriv f 0 = 0 := by
    have hh := even_deriv_neg_finite f hf he 0
    simp only [neg_zero] at hh
    linarith
  have hh := hadamard_factorization (deriv f) (contDiff_infty_iff_deriv.mp hf).2 0 x
  rw [h0,sub_zero,sub_zero,smul_eq_mul] at hh
  unfold radialSquareDerivative
  linarith

/-- Explicit finite Taylor extension in squared radius. The initial
negative branch is constant; each integration appends its next genuine
Taylor coefficient from the regularized even radial derivative. -/
def evenSquareFiniteExtension : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0,f,q => f (Real.sqrt q)
  | m+1,f,q => f 0+∫ t in (0 : ℝ)..q,
      evenSquareFiniteExtension m (radialSquareDerivative f) t

/-- Every finite derivative order is obtained from actual smooth evenness,
without any endpoint regularity premise. The extension may depend on m. -/
theorem evenSquareFiniteExtension_regular (m : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (he : Function.Even f) :
    ContDiff ℝ (m : ℕ∞ω) (evenSquareFiniteExtension m f) ∧
      ∀ r : ℝ, evenSquareFiniteExtension m f (r^2) = f r := by
  induction m generalizing f with
  | zero =>
    constructor
    · exact contDiff_zero.mpr (hf.continuous.comp Real.continuous_sqrt)
    · intro r
      simp only [evenSquareFiniteExtension,Real.sqrt_sq_eq_abs]
      by_cases hr : 0 ≤ r
      · rw [abs_of_nonneg hr]
      · rw [abs_of_neg (lt_of_not_ge hr)]
        exact he r
  | succ m ih =>
    have hTf := radialSquareDerivative_smooth f hf
    have heTf := radialSquareDerivative_even f hf he
    obtain ⟨hH,hHr⟩ := ih (radialSquareDerivative f) hTf heTf
    let H := evenSquareFiniteExtension m (radialSquareDerivative f)
    have hHC : Continuous H := hH.continuous
    have hD (q : ℝ) : HasDerivAt (evenSquareFiniteExtension (m+1) f) (H q) q := by
      exact (intervalIntegral.integral_hasDerivAt_right (hHC.intervalIntegrable 0 q)
        hHC.aestronglyMeasurable.stronglyMeasurableAtFilter hHC.continuousAt).const_add (f 0)
    constructor
    · rw [show ((m+1 : ℕ) : ℕ∞ω) = (m : ℕ∞ω)+1 by simp,contDiff_succ_iff_deriv]
      refine ⟨fun q => (hD q).differentiableAt,by simp,?_⟩
      have hder : deriv (evenSquareFiniteExtension (m+1) f) = H :=
        funext (fun q => (hD q).deriv)
      rw [hder]
      exact hH
    · have hZ (r : ℝ) : HasDerivAt
          (fun r => evenSquareFiniteExtension (m+1) f (r^2)-f r) 0 r := by
        have hc := ((hD (r^2)).comp r ((hasDerivAt_id r).pow 2)).sub
          (hf.differentiable (by simp) r).hasDerivAt
        have hr : H (r^2)*(2*r)-deriv f r = 0 := by
          change evenSquareFiniteExtension m (radialSquareDerivative f) (r^2)*(2*r)-deriv f r = 0
          rw [hHr,even_deriv_square_factor f hf he]
          ring
        simpa only [Function.comp_def,Pi.pow_apply,Pi.sub_apply,id_eq,Nat.cast_ofNat,
          Nat.reduceSub,pow_one,one_mul,mul_one,hr] using! hc
      intro r
      apply sub_eq_zero.mp
      calc
        _ = evenSquareFiniteExtension (m+1) f ((0 : ℝ)^2)-f 0 :=
          is_const_of_deriv_eq_zero (fun r => (hZ r).differentiableAt)
            (fun r => (hZ r).deriv) r 0
        _ = 0 := by simp [evenSquareFiniteExtension]

theorem smooth_even_exists_finite_square_profile (m : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (he : Function.Even f) :
    ∃ H : ℝ → ℝ, ContDiff ℝ (m : ℕ∞ω) H ∧ ∀ r : ℝ, H (r^2) = f r :=
  ⟨evenSquareFiniteExtension m f,evenSquareFiniteExtension_regular m f hf he⟩

theorem smooth_even_exists_C3_square_profile (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (he : Function.Even f) :
    ∃ H : ℝ → ℝ, ContDiff ℝ 3 H ∧ ∀ r : ℝ, H (r^2) = f r :=
  smooth_even_exists_finite_square_profile 3 f hf he

end DFLSphere
