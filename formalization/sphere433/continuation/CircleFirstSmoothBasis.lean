import continuation.CircleFirstEigenspace
import continuation.AuxiliaryRadialSmooth

/-! Genuine smooth realization of both original first circle generators.
The original odd and radial partner equations, same-state finite pole
profiles and actual round operator produce a complete independent basis.
This includes every real field and the zero-field degeneracy. -/
noncomputable section
set_option maxHeartbeats 1200000
open Set Filter Bundle Manifold Metric Module
open scoped Topology ContDiff Manifold RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DFLPhysicalLatitude DFLSphere DFLTransverseSphere DFLActualRadial DFL.Spectral DFLWeightedSymmetry
namespace DFLCircleOdd

private theorem first_minimum_pos (r : ℝ) : 0<roundTiltMinimum 1 1 r (1/2) := by
  by_cases hr : r=0
  · rw [hr,roundTiltMinimum_zero_field]
    norm_num
  · have hh := roundTiltMinimum_physical_above_baseline 1 1 r hr
    norm_num at hh
    linarith

private theorem coord_mem (x : Circle) : (x : CircleAmbient) 0 ∈ Icc (-1 : ℝ) 1 := by
  simpa [physicalCoordinate,innerCoordFun,EuclideanSpace.inner_single_left] using
    physicalCoordinate_mem_Icc 0 x

/-- The full actual circle first eigenspace has two genuine nonzero
smooth eigenstates, one even and one odd. They are linearly independent
and every actual smooth first eigenstate has their unique two coefficients.
No mode existence, pole regularity, eigenvalue degeneracy or basis premise
is supplied. -/
theorem actual_circle_first_smooth_basis_exists (r : ℝ) :
    ∃ E O : C^∞⟮𝓡 1,Circle;ℝ⟯,
      CircleEven E ∧ CircleOdd O ∧ (∃ x,E x≠0) ∧ (∃ x,O x≠0) ∧
      (∀ x,weightedRoundApply (n := 1) circleAxis r E x=roundTiltMinimum 1 1 r (1/2)*E x) ∧
      (∀ x,weightedRoundApply (n := 1) circleAxis r O x=roundTiltMinimum 1 1 r (1/2)*O x) ∧
      (∀ u : C^∞⟮𝓡 1,Circle;ℝ⟯,
        (∀ x,weightedRoundApply (n := 1) circleAxis r u x=roundTiltMinimum 1 1 r (1/2)*u x) ↔
        ∃ cE cO : ℝ,∀ x,u x=cE*E x+cO*O x) ∧
      (∀ cE cO dE dO : ℝ,
        (∀ x,cE*E x+cO*O x=dE*E x+dO*O x) → cE=dE ∧ cO=dO) := by
  let mu := roundTiltMinimum 1 1 r (1/2)
  have hmu : mu≠0 := (first_minimum_pos r).ne'
  have hp : ‖circleAxis‖=1 := by simp [circleAxis]
  have ha : ‖circleTransverse‖=1 := by simp [circleTransverse]
  have hpa : ⟪circleTransverse,circleAxis⟫_ℝ=0 := by
    simp [circleAxis,circleTransverse,EuclideanSpace.inner_single_left]
  obtain ⟨psiO,hpsiO,hpO,sO,hsO,hpsO⟩ := original_tilt_ground_actual_witness 1 1 r (1/2)
  let gO := weightedProfileFromHalfDensity r psiO
  have hgO : ContDiff ℝ 2 gO := weightedProfileFromHalfDensity_smooth r psiO hpsiO.smooth
  have hpOg : ∀ t ∈ Icc (-1 : ℝ) 1,0<gO t := weightedProfileFromHalfDensity_positive r psiO hpO
  have heOg : LatitudeEigenEquation 3 1 1 r mu gO := by
    apply weightedProfileFromHalfDensity_eigen 3 1 1 r mu psiO hpsiO.smooth
    have hh := hpsiO.eigen
    norm_num [mu] at hh ⊢
    exact hh
  have hOsm : ContMDiff (𝓡 1) 𝓘(ℝ,ℝ) ∞ (transverseMode circleAxis circleTransverse gO) :=
    actual_auxiliary_profile_transverse_contMDiff (n := 1) circleAxis circleTransverse hp
      r psiO sO hsO hpsO
  let O : C^∞⟮𝓡 1,Circle;ℝ⟯ := ⟨transverseMode circleAxis circleTransverse gO,hOsm⟩
  have hOval (x : Circle) : O x=(x : CircleAmbient) 1*gO ((x : CircleAmbient) 0) := by
    simp [O,transverseMode,circleAxis,circleTransverse,EuclideanSpace.inner_single_left]
  have hOdd : CircleOdd O := by
    intro x
    rw [hOval,hOval,circleReflection_coord0,circleReflection_coord1]
    ring
  have hOe : ∀ x,weightedRoundApply (n := 1) circleAxis r O x=mu*O x :=
    transverseMode_weighted_eigen circleAxis circleTransverse hp hpa r mu gO hgO
      (by simpa only [Nat.cast_one] using heOg)
  obtain ⟨psiE,hpsiE3,hpsiE,hpE,sE,hsE,hpsE⟩ := original_tilt_ground_C3_actual_witness 1 1 r (3/2-2)
  let gE := weightedProfileFromHalfDensity r psiE
  have hgE3 : ContDiff ℝ 3 gE := ((contDiff_const.mul contDiff_id).exp).mul hpsiE3
  have hgE : ContDiff ℝ 2 gE := hgE3.of_le (by decide)
  have hpEg : ∀ t ∈ Icc (-1 : ℝ) 1,0<gE t := weightedProfileFromHalfDensity_positive r psiE hpE
  have hm : roundTiltMinimum 1 1 r (3/2-2)=mu := by
    have hh := circle_radial_transverse_actual_ground_eq r
    norm_num at hh ⊢
    exact hh
  have heEg : LatitudeEigenEquation 3 2 1 r mu gE := by
    have he := weightedProfileFromHalfDensity_eigen 3 2 1 r
      (roundTiltMinimum 1 1 r (3/2-2)) psiE hpsiE.smooth
      (by
        have hh := hpsiE.eigen
        norm_num at hh ⊢
        exact hh)
    rw [hm] at he
    exact he
  let fE := radialRecover 1 r mu gE
  have hfE : ContDiff ℝ 2 fE := radial_recover_smooth 1 r mu gE hgE3
  have hEsm : ContMDiff (𝓡 1) 𝓘(ℝ,ℝ) ∞ (fun x : Circle => fE ((x : CircleAmbient) 0)) := by
    have hh := actual_auxiliary_profile_radialRecover_contMDiff (n := 1) circleAxis hp r mu
      psiE hpsiE.smooth sE hsE hpsE
    simpa [circleAxis,EuclideanSpace.inner_single_left] using hh
  let E : C^∞⟮𝓡 1,Circle;ℝ⟯ := ⟨fun x => fE ((x : CircleAmbient) 0),hEsm⟩
  have hEval (x : Circle) : E x=fE ((x : CircleAmbient) 0) := rfl
  have hEven : CircleEven E := by
    intro x
    rw [hEval,hEval,circleReflection_coord0]
  have hRad := partner_eigenfunction_recovers_radial 1 r mu hmu gE hgE
    (by simpa only [Nat.cast_one] using heEg)
  have hLatRad : LatitudeEigenEquation 1 0 0 r mu fE := by
    intro t ht
    simpa only [radialApply,zero_mul,zero_add,add_zero] using hRad t ht
  have hRadClosed := latitudeEigenEquation_closed 1 0 0 r mu fE hfE hLatRad
  have hEe : ∀ x,weightedRoundApply (n := 1) circleAxis r E x=mu*E x := by
    intro x
    have hfun : (E : Circle → ℝ)=fun y : Circle => fE ⟪circleAxis,(y : CircleAmbient)⟫_ℝ := by
      funext y
      simp [E,circleAxis,EuclideanSpace.inner_single_left]
    rw [hfun,weightedRoundApply_latitude (n := 1) circleAxis hp r fE hfE x]
    have hh := hRadClosed ((x : CircleAmbient) 0) (coord_mem x)
    simpa [radialApply,circleAxis,EuclideanSpace.inner_single_left] using hh
  have hInd : ∀ cE cO : ℝ,(∀ x,cE*E x+cO*O x=0) → cE=0 ∧ cO=0 := by
    intro cE cO hz
    apply actual_circle_first_generators_independent r gO gE hpOg hpEg cE cO
    intro x
    simpa only [hEval,hOval,fE,mu] using hz x
  have hEn : ∃ x,E x≠0 := by
    by_contra h
    push Not at h
    have hh := hInd 1 0 (fun x => by simp only [h x,mul_zero,zero_mul,zero_add])
    norm_num at hh
  have hOn : ∃ x,O x≠0 := by
    by_contra h
    push Not at h
    have hh := hInd 0 1 (fun x => by simp only [h x,mul_zero,zero_mul,zero_add])
    norm_num at hh
  refine ⟨E,O,hEven,hOdd,hEn,hOn,hEe,hOe,?_,?_⟩
  · intro u
    constructor
    · intro hu
      have hpar := circle_parity_eigen r mu u hu
      obtain ⟨cE,hE⟩ := actual_circle_first_even_proportional r gE hgE hpEg heEg
        (circleEvenPart u) (circle_evenPart_even u) hpar.1
      obtain ⟨cO,hO⟩ := actual_circle_first_odd_proportional r gO hgO hpOg heOg
        (circleOddPart u) (circle_oddPart_odd u) hpar.2
      refine ⟨cE,cO,?_⟩
      intro x
      rw [← circle_even_odd_sum u x,hE x,hO x,hEval,hOval]
    · rintro ⟨cE,cO,hU⟩ x
      have hfun : (u : Circle → ℝ)=fun y => cE*E y+cO*O y := funext hU
      rw [hfun,weightedRoundApply_linear circleAxis r cE cO E O x,hEe,hOe]
      ring
  · intro cE cO dE dO heq
    have hh := hInd (cE-dE) (cO-dO) (by
      intro x
      nlinarith [heq x])
    exact ⟨sub_eq_zero.mp hh.1,sub_eq_zero.mp hh.2⟩

end DFLCircleOdd
