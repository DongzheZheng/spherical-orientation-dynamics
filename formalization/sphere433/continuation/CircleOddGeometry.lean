import continuation.PhysicalSphereLatitudeProfileC3
import continuation.RoundSphereGroundSymmetry

/-! The physical circle axis reflection and its exact two-point latitude
fibres. Smooth odd meridians have a genuine smooth even Hadamard quotient. -/
noncomputable section
set_option maxHeartbeats 800000
open Set Filter Function Metric Manifold
open scoped Topology ContDiff Manifold RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis.Calculus
open DFLPhysicalLatitude DFLSphere
namespace DFLCircleOdd
abbrev CircleAmbient := PhysicalAmbient 0
abbrev Circle := PhysicalSphere 0
def circleAxis : CircleAmbient := EuclideanSpace.single 0 1
def circleTransverse : CircleAmbient := EuclideanSpace.single 1 1
def circleReflectionEquiv : CircleAmbient ≃ₗᵢ[ℝ] CircleAmbient :=
  (ℝ ∙ circleAxis).reflection
def circleReflection : Circle → Circle := sphereDiffeo (n := 1) circleReflectionEquiv

theorem circleReflection_coord0 (x : Circle) :
    (circleReflection x : CircleAmbient) 0 = (x : CircleAmbient) 0 := by
  change (circleReflectionEquiv (x : CircleAmbient)) 0 = _
  rw [circleReflectionEquiv,Submodule.reflection_singleton_apply]
  simp [circleAxis,EuclideanSpace.inner_single_left]
  ring

theorem circleReflection_coord1 (x : Circle) :
    (circleReflection x : CircleAmbient) 1 = -(x : CircleAmbient) 1 := by
  change (circleReflectionEquiv (x : CircleAmbient)) 1 = _
  rw [circleReflectionEquiv,Submodule.reflection_singleton_apply]
  simp [circleAxis,EuclideanSpace.inner_single_left]

theorem circle_norm_identity (x : Circle) :
    ((x : CircleAmbient) 0)^2+((x : CircleAmbient) 1)^2 = 1 := by
  have hh := EuclideanSpace.real_norm_sq_eq (x : CircleAmbient)
  rw [norm_eq_of_mem_sphere x] at hh
  simpa [Fin.sum_univ_two] using hh.symm

theorem circle_ext (x y : Circle)
    (h0 : (x : CircleAmbient) 0 = (y : CircleAmbient) 0)
    (h1 : (x : CircleAmbient) 1 = (y : CircleAmbient) 1) : x = y := by
  apply Subtype.ext
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- A true circle latitude fibre consists of a point and its reflection. -/
theorem circle_same_latitude (x y : Circle)
    (h0 : (x : CircleAmbient) 0 = (y : CircleAmbient) 0) :
    x = y ∨ x = circleReflection y := by
  have hx := circle_norm_identity x
  have hy := circle_norm_identity y
  have hs : ((x : CircleAmbient) 1)^2 = ((y : CircleAmbient) 1)^2 := by
    rw [h0] at hx
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
  · exact Or.inl (circle_ext x y h0 he)
  · exact Or.inr (circle_ext x (circleReflection y)
      (by rw [circleReflection_coord0]; exact h0)
      (by rw [circleReflection_coord1]; exact he))

def CircleOdd (u : Circle → ℝ) : Prop := ∀ x, u (circleReflection x) = -u x

/-- Odd factorization at one representative transfers to its whole
actual circle latitude fibre. -/
theorem circle_odd_factor_transfer (u : Circle → ℝ) (hu : CircleOdd u)
    (v : ℝ → ℝ) (x y : Circle)
    (h0 : (x : CircleAmbient) 0 = (y : CircleAmbient) 0)
    (hy : u y = (y : CircleAmbient) 1*v ((y : CircleAmbient) 0)) :
    u x = (x : CircleAmbient) 1*v ((x : CircleAmbient) 0) := by
  rcases circle_same_latitude x y h0 with rfl | rfl
  · exact hy
  · rw [hu y,circleReflection_coord1,circleReflection_coord0,hy]
    ring

theorem circle_odd_zero_on_axis (u : Circle → ℝ) (hu : CircleOdd u)
    (x : Circle) (hx : (x : CircleAmbient) 1 = 0) : u x = 0 := by
  have hr : circleReflection x = x := circle_ext _ _
    (circleReflection_coord0 x) (by rw [circleReflection_coord1,hx]; simp)
  have hh := hu x
  rw [hr] at hh
  linarith

def circlePoleMeridian (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) : Circle :=
  physicalMeridian 0 0 1 (by norm_num) eps heps r

theorem circlePoleMeridian_coord0 (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    (circlePoleMeridian eps heps r : CircleAmbient) 0 = eps/Real.sqrt (1+r^2) := by
  simp [circlePoleMeridian,physicalMeridian,physicalMeridianAmbient,div_eq_mul_inv,mul_comm]

theorem circlePoleMeridian_coord1 (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    (circlePoleMeridian eps heps r : CircleAmbient) 1 = r/Real.sqrt (1+r^2) := by
  simp [circlePoleMeridian,physicalMeridian,physicalMeridianAmbient,div_eq_mul_inv,mul_comm]

theorem circlePoleMeridian_reflection (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    circleReflection (circlePoleMeridian eps heps r) = circlePoleMeridian eps heps (-r) := by
  apply circle_ext
  · rw [circleReflection_coord0,circlePoleMeridian_coord0,circlePoleMeridian_coord0,neg_sq]
  · rw [circleReflection_coord1,circlePoleMeridian_coord1,circlePoleMeridian_coord1,neg_sq,neg_div]

def circlePoleValue (u : Circle → ℝ) (eps : ℝ) (heps : eps^2 = 1) : ℝ → ℝ :=
  fun r => u (circlePoleMeridian eps heps r)

def circlePoleFactor (u : Circle → ℝ) (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) : ℝ :=
  Real.sqrt (1+r^2)*hadamardFactor (circlePoleValue u eps heps) 0 r

/-- True odd smooth functions are divisible by radius with a smooth
even quotient, including at radius zero. -/
theorem smooth_odd_hadamard_even (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hodd : Function.Odd F) :
    ContDiff ℝ ∞ (hadamardFactor F 0) ∧ Function.Even (hadamardFactor F 0) ∧
      ∀ r, F r = r*hadamardFactor F 0 r := by
  have h0 : F 0 = 0 := by have hh := hodd 0; simp only [neg_zero] at hh; linarith
  have hfac : ∀ r, F r = r*hadamardFactor F 0 r := by
    intro r
    simpa only [h0,sub_zero,smul_eq_mul] using hadamard_factorization F hF 0 r
  refine ⟨hadamardFactor_contDiff F hF 0,?_,hfac⟩
  intro r
  by_cases hr : r = 0
  · simp [hr]
  · have hp := hfac r
    have hn := hfac (-r)
    rw [hodd r] at hn
    have he : r*hadamardFactor F 0 (-r) = r*hadamardFactor F 0 r := by linarith
    exact mul_left_cancel₀ hr he

/-- The meridian factor after division by the true transverse coordinate
is smooth even, hence has the already verified squared-radius regularity. -/
theorem circlePoleFactor_smooth_even
    (u : C^∞⟮𝓡 1, Circle; ℝ⟯) (hu : CircleOdd u)
    (eps : ℝ) (heps : eps^2 = 1) :
    ContDiff ℝ ∞ (circlePoleFactor u eps heps) ∧
      Function.Even (circlePoleFactor u eps heps) := by
  have hF : ContDiff ℝ ∞ (circlePoleValue u eps heps) :=
    (u.contMDiff.comp (physicalMeridian_smooth 0 0 1 (by norm_num) eps heps)).contDiff
  have ho : Function.Odd (circlePoleValue u eps heps) := by
    intro r
    change u (circlePoleMeridian eps heps (-r)) = -u (circlePoleMeridian eps heps r)
    rw [← circlePoleMeridian_reflection]
    exact hu _
  obtain ⟨hH,he,_⟩ := smooth_odd_hadamard_even _ hF ho
  have hs : ContDiff ℝ ∞ (fun r : ℝ => Real.sqrt (1+r^2)) :=
    (by fun_prop : ContDiff ℝ ∞ (fun r : ℝ => 1+r^2)).sqrt (by intro r; positivity)
  refine ⟨hs.mul hH,?_⟩
  intro r
  dsimp [circlePoleFactor]
  rw [neg_sq,he r]

/-- Actual pole-meridian factorization with the regularized factor. -/
theorem circlePoleValue_factor (u : C^∞⟮𝓡 1, Circle; ℝ⟯) (hu : CircleOdd u)
    (eps : ℝ) (heps : eps^2 = 1) (r : ℝ) :
    u (circlePoleMeridian eps heps r) =
      (circlePoleMeridian eps heps r : CircleAmbient) 1 *circlePoleFactor u eps heps r := by
  have hF : ContDiff ℝ ∞ (circlePoleValue u eps heps) :=
    (u.contMDiff.comp (physicalMeridian_smooth 0 0 1 (by norm_num) eps heps)).contDiff
  have ho : Function.Odd (circlePoleValue u eps heps) := by
    intro y
    change u (circlePoleMeridian eps heps (-y)) = -u (circlePoleMeridian eps heps y)
    rw [← circlePoleMeridian_reflection]
    exact hu _
  have hh := (smooth_odd_hadamard_even _ hF ho).2.2 r
  rw [circlePoleMeridian_coord1]
  dsimp [circlePoleFactor]
  have hs : Real.sqrt (1+r^2) ≠ 0 := by positivity
  rw [← mul_assoc,div_mul_cancel₀ r hs]
  exact hh

end DFLCircleOdd
