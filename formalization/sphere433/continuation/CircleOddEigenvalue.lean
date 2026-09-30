import continuation.CircleOddProfile
import continuation.RadialEigenvalueLower

/-! The actual smooth odd-circle eigenstate reduces to the manuscript's
M=3,b=1 auxiliary equation and its actual ground lower bound. -/
noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Bundle Manifold Metric Module
open scoped Topology Interval ContDiff Manifold RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DFLPhysicalLatitude DFLSphere DFLTransverseSphere
namespace DFL.Spectral

/-- Every nonzero original C² latitude eigenprofile is bounded below by
the actual auxiliary-sphere ground. No Rayleigh or existence input remains. -/
theorem latitude_eigenvalue_ge_actual_ground (M : ℕ) (hM : 2 ≤ M)
    (b lam0 r lam : ℝ) (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (he : LatitudeEigenEquation M b lam0 r lam v)
    (hne : ∃ t ∈ Ioo (-1 : ℝ) 1, v t ≠ 0) :
    roundTiltMinimum (M-2) lam0 r ((M : ℝ)/2-b) ≤ lam := by
  have heclosed := latitudeEigenEquation_closed M b lam0 r lam v hv he
  let u := halfDensityLift r v
  have hu : ContDiff ℝ 2 u := halfDensityLift_smooth r v hv
  have hue : ∀ t ∈ Icc (-1 : ℝ) 1,
      tiltApply M lam0 r ((M : ℝ)/2-b) u t = lam*u t := by
    intro t ht
    have hb : (M : ℝ)/2-((M : ℝ)/2-b) = b := by ring
    change halfDensityApply M _ lam0 r (halfDensityLift r v) t = _
    rw [hb,halfDensityApply_lift M b lam0 r v hv t,heclosed t ht]
    dsimp [u,halfDensityLift]
    ring
  have hune : ∃ t ∈ Ioo (-1 : ℝ) 1, u t ≠ 0 := by
    obtain ⟨t,ht,hvne⟩ := hne
    exact ⟨t,ht,mul_ne_zero (Real.exp_ne_zero _) hvne⟩
  have hnorm := latitudeNorm_pos_of_nonzero M hM 0 u hu.continuous hune
  obtain ⟨g,hg,_⟩ := original_tilt_ground_exists_ge_two M hM lam0 r ((M : ℝ)/2-b)
  have hbound := hg.rayleigh u hu
  have henergy : tiltPair M lam0 r ((M : ℝ)/2-b) u u = lam*latitudeNorm M 0 u := by
    unfold tiltPair latitudeNorm
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have htcc : t ∈ Icc (-1 : ℝ) 1 := by simpa using ht
    dsimp only
    rw [hue t htcc]
    ring
  rw [henergy] at hbound
  exact le_of_mul_le_mul_right hbound hnorm

end DFL.Spectral
namespace DFLCircleOdd
open DFL.Spectral

def circleLatitudeApply (r : ℝ) (v : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(1-t^2)*deriv (deriv v) t+(3*t-r*(1-t^2))*deriv v t+(1+r*t)*v t

/-- The odd mode calculation uses the actual round Laplacian and drift. -/
theorem weightedRoundApply_circle_mode (r : ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (x : Circle) :
    weightedRoundApply (n := 1) circleAxis r (transverseMode circleAxis circleTransverse v) x =
      (x : CircleAmbient) 1*circleLatitudeApply r v ((x : CircleAmbient) 0) := by
  unfold weightedRoundApply transverseMode
  rw [transverse_laplacian (n := 1) circleAxis circleTransverse (by simp [circleAxis])
    (by simp [circleAxis,circleTransverse,EuclideanSpace.inner_single_left]) v hv x,
    transverse_drift (n := 1) circleAxis circleTransverse (by simp [circleAxis])
    (by simp [circleAxis,circleTransverse,EuclideanSpace.inner_single_left]) v hv x]
  unfold circleLatitudeApply
  simp only [circleAxis,circleTransverse,EuclideanSpace.inner_single_left]
  norm_num
  ring

private theorem circle_coordinate_eq (x : Circle) :
    (physicalCoordinate 0).toFun x = (x : CircleAmbient) 0 := by
  simp [physicalCoordinate,DifferentialGeometry.Geometry.innerCoordFun,EuclideanSpace.inner_single_left]

/-- A genuine smooth odd circle eigenfunction supplies the C² original
auxiliary profile and equation, with both poles controlled by Hadamard. -/
theorem actual_circle_odd_eigenprofile (r lam : ℝ)
    (u : C^∞⟮𝓡 1, Circle; ℝ⟯) (hu : CircleOdd u)
    (heig : ∀ x, weightedRoundApply (n := 1) circleAxis r u x = lam*u x) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧
      (∀ x, u x = (x : CircleAmbient) 1*v ((x : CircleAmbient) 0)) ∧
      LatitudeEigenEquation 3 1 1 r lam v := by
  obtain ⟨v,hv,hvu⟩ := circle_smooth_odd_exists_C2_profile u hu
  refine ⟨v,hv,hvu,?_⟩
  have hfun : (u : Circle → ℝ) = transverseMode circleAxis circleTransverse v := by
    funext x
    simpa [transverseMode,circleAxis,circleTransverse,EuclideanSpace.inner_single_left] using hvu x
  intro t ht
  obtain ⟨x,hx⟩ := physicalCoordinate_surjective_Icc 0 t ⟨ht.1.le,ht.2.le⟩
  have hx0 : (x : CircleAmbient) 0 = t := by rw [circle_coordinate_eq] at hx; exact hx
  have hx1 : (x : CircleAmbient) 1 ≠ 0 := by
    intro hz
    have hn := circle_norm_identity x
    rw [hx0,hz] at hn
    nlinarith [ht.1,ht.2]
  have hh := heig x
  rw [hfun,weightedRoundApply_circle_mode r v hv x] at hh
  have hmode : transverseMode circleAxis circleTransverse v x =
      (x : CircleAmbient) 1*v ((x : CircleAmbient) 0) := by
    simp [transverseMode,circleAxis,circleTransverse,EuclideanSpace.inner_single_left]
  rw [hmode,hx0] at hh
  have he : circleLatitudeApply r v t = lam*v t := by
    apply mul_left_cancel₀ hx1
    calc
      (x : CircleAmbient) 1*circleLatitudeApply r v t = lam*((x : CircleAmbient) 1*v t) := hh
      _ = (x : CircleAmbient) 1*(lam*v t) := by ring
  simpa [circleLatitudeApply] using he

/-- The physical circle's genuine odd smooth sector has the exact
actual first-transverse lower bound. No endpoint, quotient, norm,
Rayleigh, ground existence, or λ-positivity premise is supplied. -/
theorem actual_circle_odd_eigenvalue_ge_transverse_ground (r lam : ℝ)
    (u : C^∞⟮𝓡 1, Circle; ℝ⟯) (hu : CircleOdd u)
    (heig : ∀ x, weightedRoundApply (n := 1) circleAxis r u x = lam*u x)
    (hne : ∃ x, u x ≠ 0) :
    roundTiltMinimum 1 1 r (1/2) ≤ lam := by
  obtain ⟨v,hv,hvu,he⟩ := actual_circle_odd_eigenprofile r lam u hu heig
  have hvne : ∃ t ∈ Ioo (-1 : ℝ) 1, v t ≠ 0 := by
    obtain ⟨x,hx⟩ := hne
    have hxv : (x : CircleAmbient) 1*v ((x : CircleAmbient) 0) ≠ 0 := by rw [← hvu x]; exact hx
    have hx1 : (x : CircleAmbient) 1 ≠ 0 := (mul_ne_zero_iff.mp hxv).1
    have hv0 : v ((x : CircleAmbient) 0) ≠ 0 := (mul_ne_zero_iff.mp hxv).2
    have hn := circle_norm_identity x
    have hsq := sq_pos_of_ne_zero hx1
    refine ⟨(x : CircleAmbient) 0,⟨?_,?_⟩,hv0⟩ <;> nlinarith
  have hbound := latitude_eigenvalue_ge_actual_ground 3 (by omega) 1 1 r lam v hv he hvne
  norm_num at hbound
  exact hbound

end DFLCircleOdd
