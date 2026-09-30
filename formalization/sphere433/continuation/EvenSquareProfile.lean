import DifferentialGeometry.Analysis.Calculus.Taylor
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BoundaryDerivLimit
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Piecewise
import Mathlib.Algebra.Group.EvenFunction

/-! Pole regularity mechanism: an actual smooth even meridian function is
C2 in squared radius, with a global C2 extension across radius-square zero. -/
noncomputable section
set_option maxHeartbeats 800000
open Set Filter Function
open scoped Topology ContDiff
namespace DFLSphere
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Analysis.Calculus.SmoothExtension

/-- Division of the odd radial derivative by twice the radius, regularized
by the actual Hadamard integral. -/
def radialSquareDerivative (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (1/2 : ℝ)*hadamardFactor (deriv f) 0 x

private theorem even_deriv_neg (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (x : ℝ) :
    deriv f (-x) = -deriv f x := by
  have hcomp := ((hf.differentiable (by simp) (-x)).hasDerivAt).comp x
    (hasDerivAt_id x).neg
  have heq : (fun y => f (-y)) = f := funext he
  change HasDerivAt (fun y => f (-y)) (deriv f (-x)*(-1)) x at hcomp
  rw [heq] at hcomp
  have hd := hcomp.deriv
  linarith

private theorem even_deriv_zero (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) :
    deriv f 0 = 0 := by
  have hh := even_deriv_neg f hf he 0
  simp only [neg_zero] at hh
  linarith

theorem radialSquareDerivative_smooth (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (radialSquareDerivative f) :=
  contDiff_const.mul (hadamardFactor_contDiff (deriv f) (contDiff_infty_iff_deriv.mp hf).2 0)

private theorem even_deriv_factor (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) (x : ℝ) :
    deriv f x = 2*x*radialSquareDerivative f x := by
  have hh := hadamard_factorization (deriv f) (contDiff_infty_iff_deriv.mp hf).2 0 x
  rw [even_deriv_zero f hf he,sub_zero,sub_zero,smul_eq_mul] at hh
  unfold radialSquareDerivative
  linarith

theorem radialSquareDerivative_even (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) :
    Function.Even (radialSquareDerivative f) := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have hp := even_deriv_factor f hf he x
    have hn := even_deriv_factor f hf he (-x)
    rw [even_deriv_neg f hf he x] at hn
    have hh : (2*x)*radialSquareDerivative f (-x) = (2*x)*radialSquareDerivative f x := by
      linarith
    exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hx) hh

private theorem sqrt_even_hasDerivAt (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun q => f (Real.sqrt q)) (radialSquareDerivative f (Real.sqrt q)) q := by
  have hh := ((hf.differentiable (by simp) (Real.sqrt q)).hasDerivAt).comp q
    (Real.hasDerivAt_sqrt (ne_of_gt hq))
  have hs : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  have hd := even_deriv_factor f hf he (Real.sqrt q)
  have heq : deriv f (Real.sqrt q)*(1/(2*Real.sqrt q)) = radialSquareDerivative f (Real.sqrt q) := by
    rw [hd]
    field_simp
  simpa only [Function.comp_def,heq] using hh

/-- Global C2 extension of the squared-radius profile. The negative side
is the second Taylor polynomial, used only to state ordinary global C2. -/
def evenSquareExtension (f : ℝ → ℝ) (q : ℝ) : ℝ :=
  if q ≤ 0 then f 0+q*radialSquareDerivative f 0+
      q^2/2*radialSquareDerivative (radialSquareDerivative f) 0
    else f (Real.sqrt q)

private def evenSquareFirst (f : ℝ → ℝ) (q : ℝ) : ℝ :=
  if q ≤ 0 then radialSquareDerivative f 0+q*radialSquareDerivative (radialSquareDerivative f) 0
    else radialSquareDerivative f (Real.sqrt q)

private def evenSquareSecond (f : ℝ → ℝ) (q : ℝ) : ℝ :=
  if q ≤ 0 then radialSquareDerivative (radialSquareDerivative f) 0
    else radialSquareDerivative (radialSquareDerivative f) (Real.sqrt q)

private theorem continuous_split_zero {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h0 : f 0 = g 0) : Continuous (fun q => if q ≤ 0 then f q else g q) := by
  have hfront : ∀ x ∈ frontier (Iic (0 : ℝ)), f x = g x := by
    intro x hx
    have hx0 : x = 0 := by simpa only [frontier_Iic,mem_singleton_iff] using hx
    simpa only [hx0] using h0
  exact hf.if hfront hg

private theorem evenSquareFirst_continuous (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    Continuous (evenSquareFirst f) := by
  apply continuous_split_zero
  · fun_prop
  · exact (radialSquareDerivative_smooth f hf).continuous.comp Real.continuous_sqrt
  · simp

private theorem evenSquareSecond_continuous (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    Continuous (evenSquareSecond f) := by
  apply continuous_split_zero continuous_const
    ((radialSquareDerivative_smooth (radialSquareDerivative f)
      (radialSquareDerivative_smooth f hf)).continuous.comp Real.continuous_sqrt)
  simp

private theorem evenSquareExtension_hasDerivAt (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (q : ℝ) :
    HasDerivAt (evenSquareExtension f) (evenSquareFirst f q) q := by
  let A := radialSquareDerivative f 0
  let B := radialSquareDerivative (radialSquareDerivative f) 0
  have hleft (t : ℝ) : HasDerivAt (fun q : ℝ => f 0+q*A+q^2/2*B) (A+t*B) t := by
    convert! ((hasDerivAt_const t (f 0)).add ((hasDerivAt_id t).mul_const A)).add
      (((hasDerivAt_id t).pow 2).div_const 2 |>.mul_const B) using 1; first | rfl | (dsimp; ring)
  by_cases hq : q = 0
  · subst q
    rw [evenSquareFirst,if_pos le_rfl]
    simp only [zero_mul,add_zero]
    change HasDerivAt (fun t => if t ≤ 0 then f 0+t*A+t^2/2*B else f (Real.sqrt t)) A 0
    have hz : HasDerivAt (fun t => if t ≤ 0 then f 0+t*A+t^2/2*B else f (Real.sqrt t)) (A+0*B) 0 := by
      apply hasDerivAt_ite_of_continuous_derivatives (a := -1) (s := 0) (b := 1)
        (FL := fun t => A+t*B) (FR := fun t => radialSquareDerivative f (Real.sqrt t)) (by norm_num) (by norm_num)
      · exact (by fun_prop : Continuous (fun t : ℝ => f 0+t*A+t^2/2*B)).continuousAt.continuousWithinAt
      · exact (hf.continuous.comp Real.continuous_sqrt).continuousAt.continuousWithinAt
      · intro t _; exact hleft t
      · intro t ht; exact sqrt_even_hasDerivAt f hf he ht.1
      · simp
      · exact (by fun_prop : Continuous (fun t : ℝ => A+t*B)).continuousAt.continuousWithinAt
      · exact ((radialSquareDerivative_smooth f hf).continuous.comp Real.continuous_sqrt).continuousAt.continuousWithinAt
      · simp [A]
    simpa only [zero_mul,add_zero] using! hz
  · rcases lt_or_gt_of_ne hq with hneg | hpos
    · change HasDerivAt (evenSquareExtension f) _ q
      rw [evenSquareFirst,if_pos hneg.le]
      exact (hleft q).congr_of_eventuallyEq (by
        filter_upwards [isOpen_Iio.mem_nhds hneg] with t ht
        simp only [evenSquareExtension,if_pos (show t ≤ 0 from (show t < 0 from ht).le)]
        rfl)
    · rw [evenSquareFirst,if_neg (not_le_of_gt hpos)]
      exact (sqrt_even_hasDerivAt f hf he hpos).congr_of_eventuallyEq (by
        filter_upwards [isOpen_Ioi.mem_nhds hpos] with t ht
        simp only [evenSquareExtension,if_neg (not_le_of_gt (show 0 < t from ht))])

private theorem evenSquareFirst_hasDerivAt (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (q : ℝ) :
    HasDerivAt (evenSquareFirst f) (evenSquareSecond f q) q := by
  let A := radialSquareDerivative f 0
  let B := radialSquareDerivative (radialSquareDerivative f) 0
  have hT := radialSquareDerivative_smooth f hf
  have heT := radialSquareDerivative_even f hf he
  have hleft (t : ℝ) : HasDerivAt (fun q : ℝ => A+q*B) B t := by
    simpa only [one_mul,id_eq] using! ((hasDerivAt_id t).mul_const B).const_add A
  by_cases hq : q = 0
  · subst q
    rw [evenSquareSecond,if_pos le_rfl]
    change HasDerivAt (fun t => if t ≤ 0 then A+t*B else radialSquareDerivative f (Real.sqrt t)) B 0
    apply hasDerivAt_ite_of_continuous_derivatives (a := -1) (s := 0) (b := 1)
      (FL := fun _ => B) (FR := fun t => radialSquareDerivative (radialSquareDerivative f) (Real.sqrt t)) (by norm_num) (by norm_num)
    · exact (by fun_prop : Continuous (fun t : ℝ => A+t*B)).continuousAt.continuousWithinAt
    · exact (hT.continuous.comp Real.continuous_sqrt).continuousAt.continuousWithinAt
    · intro t _; exact hleft t
    · intro t ht; exact sqrt_even_hasDerivAt _ hT heT ht.1
    · simp [A]
    · exact continuous_const.continuousAt.continuousWithinAt
    · exact ((radialSquareDerivative_smooth _ hT).continuous.comp Real.continuous_sqrt).continuousAt.continuousWithinAt
    · simp [B]
  · rcases lt_or_gt_of_ne hq with hneg | hpos
    · rw [evenSquareSecond,if_pos hneg.le]
      exact (hleft q).congr_of_eventuallyEq (by
        filter_upwards [isOpen_Iio.mem_nhds hneg] with t ht
        simp only [evenSquareFirst,if_pos (show t ≤ 0 from (show t < 0 from ht).le)]
        rfl)
    · rw [evenSquareSecond,if_neg (not_le_of_gt hpos)]
      exact (sqrt_even_hasDerivAt _ hT heT hpos).congr_of_eventuallyEq (by
        filter_upwards [isOpen_Ioi.mem_nhds hpos] with t ht
        simp only [evenSquareFirst,if_neg (not_le_of_gt (show 0 < t from ht))])

/-- No endpoint regularity assumption: it follows from smooth evenness
through Hadamard division and the proved one-sided derivative gluing. -/
theorem evenSquareExtension_contDiff_two (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) :
    ContDiff ℝ 2 (evenSquareExtension f) := by
  have hD : deriv (evenSquareExtension f) = evenSquareFirst f :=
    funext (fun q => (evenSquareExtension_hasDerivAt f hf he q).deriv)
  have hDD : deriv (evenSquareFirst f) = evenSquareSecond f :=
    funext (fun q => (evenSquareFirst_hasDerivAt f hf he q).deriv)
  have hfirst : ContDiff ℝ 1 (evenSquareFirst f) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun q => (evenSquareFirst_hasDerivAt f hf he q).differentiableAt,?_⟩
    rw [hDD]
    exact evenSquareSecond_continuous f hf
  rw [show (2 : ℕ∞ω) = 1+1 from rfl,contDiff_succ_iff_deriv]
  refine ⟨fun q => (evenSquareExtension_hasDerivAt f hf he q).differentiableAt,by simp,?_⟩
  rw [hD]
  exact hfirst

theorem evenSquareExtension_eq_sqrt (f : ℝ → ℝ) {q : ℝ} (hq : 0 ≤ q) :
    evenSquareExtension f q = f (Real.sqrt q) := by
  rcases eq_or_lt_of_le hq with hzero | hpos
  · simp [← hzero,evenSquareExtension]
  · simp only [evenSquareExtension,if_neg (not_le_of_gt hpos)]

theorem smooth_even_exists_C2_square_profile (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (he : Function.Even f) :
    ∃ H : ℝ → ℝ, ContDiff ℝ 2 H ∧ ∀ r : ℝ, H (r^2) = f r := by
  refine ⟨evenSquareExtension f,evenSquareExtension_contDiff_two f hf he,?_⟩
  intro r
  rw [evenSquareExtension_eq_sqrt f (sq_nonneg r),Real.sqrt_sq_eq_abs]
  by_cases hr : 0 ≤ r
  · rw [abs_of_nonneg hr]
  · rw [abs_of_neg (lt_of_not_ge hr)]
    exact he r
end DFLSphere
