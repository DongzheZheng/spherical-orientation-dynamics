import continuation.OriginalTiltEigenspaceSimple
import continuation.CircleParity
import continuation.TiltDriftClassification

/-! The original circle first-eigenstate classification. The true odd
Hadamard profile and true even C³ pole profile reduce to the two original
M=3 amplitude problems. Their actual positive grounds span each sector;
the actual reflection split gives the complete two-generator span. -/
noncomputable section
set_option maxHeartbeats 1000000
open Set Filter Bundle Manifold Metric Module
open scoped Topology ContDiff Manifold RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DFLPhysicalLatitude DFLSphere DFLTransverseSphere DFLActualRadial DFL.Spectral

namespace DFL.Spectral

/-- The original D*D reconstruction removes the integration constant.
If the derivative of a C³ radial eigenprofile is proportional to an
original C² partner profile, the eigenprofile itself is proportional
to D*partner/λ on the whole physical interval. -/
theorem radial_eigenprofile_recover_proportional (d : ℕ) (r lam c : ℝ) (hlam : lam≠0)
    (f g : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 2 g)
    (he : RadialEigenEquation d r lam f)
    (hder : ∀ t ∈ Icc (-1 : ℝ) 1,deriv f t=c*g t) :
    ∀ t ∈ Icc (-1 : ℝ) 1,f t=c*radialRecover d r lam g t := by
  have hI : EqOn f (fun t => c*radialRecover d r lam g t) (Ioo (-1 : ℝ) 1) := by
    intro t ht
    have hl : deriv f =ᶠ[𝓝 t] (fun y => c*g y) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy
      exact hder y ⟨hy.1.le,hy.2.le⟩
    have hdd := hl.deriv_eq
    rw [((hg.differentiable (by norm_num) t).hasDerivAt.const_mul c).deriv] at hdd
    calc
      f t=radialRecover d r lam (deriv f) t :=
        (radial_recover_derivative_eigenfunction d r lam hlam f he ht).symm
      _=c*radialRecover d r lam g t := by
        dsimp only [radialRecover,radialAdjoint]
        rw [hder t ⟨ht.1.le,ht.2.le⟩,hdd]
        ring
  have hc : Continuous (radialRecover d r lam g) := by
    have hgd : Continuous (deriv g) := (hg.deriv' : ContDiff ℝ 1 (deriv g)).continuous
    change Continuous (fun t => (-(1-t^2)*deriv g t+((d : ℝ)*t-r*(1-t^2))*g t)/lam)
    fun_prop
  have hcl := hI.closure hf.continuous (continuous_const.mul hc)
  rw [closure_Ioo (by norm_num : (-1 : ℝ)≠1)] at hcl
  exact hcl

end DFL.Spectral
namespace DFLCircleOdd

private theorem circle_first_minimum_pos (r : ℝ) : 0<roundTiltMinimum 1 1 r (1/2) := by
  by_cases hr : r=0
  · rw [hr,roundTiltMinimum_zero_field]
    norm_num
  · have hh := roundTiltMinimum_physical_above_baseline 1 1 r hr
    norm_num at hh
    linarith

private theorem circle_coord0_mem (x : Circle) : (x : CircleAmbient) 0 ∈ Icc (-1 : ℝ) 1 := by
  simpa [physicalCoordinate,innerCoordFun,EuclideanSpace.inner_single_left] using
    physicalCoordinate_mem_Icc 0 x

/-- Every genuine odd smooth circle first eigenstate is proportional to
one positive original M=3,b=1 profile. The actual odd factor and its pole
regularity are proved by Hadamard; no factorization premise is supplied. -/
theorem actual_circle_first_odd_proportional (r : ℝ) (g : ℝ → ℝ)
    (hg : ContDiff ℝ 2 g) (hpos : ∀ t ∈ Icc (-1 : ℝ) 1,0<g t)
    (he : LatitudeEigenEquation 3 1 1 r (roundTiltMinimum 1 1 r (1/2)) g)
    (u : C^∞⟮𝓡 1,Circle;ℝ⟯) (hu : CircleOdd u)
    (heig : ∀ x,weightedRoundApply (n := 1) circleAxis r u x=roundTiltMinimum 1 1 r (1/2)*u x) :
    ∃ c : ℝ,∀ x,u x=c*((x : CircleAmbient) 1*g ((x : CircleAmbient) 0)) := by
  obtain ⟨v,hv,hvu,hve⟩ := actual_circle_odd_eigenprofile r _ u hu heig
  obtain ⟨c,hc⟩ := original_weighted_eigenprofile_proportional 3 (by omega) 1 1 r _
    g v hg hv hpos he hve
  refine ⟨c,?_⟩
  intro x
  rw [hvu x,hc _ (circle_coord0_mem x)]
  ring

/-- Every genuine even smooth circle first eigenstate is proportional
to the original D* reconstruction of one positive M=3,b=2 ground.
The true C³ pole profile and the nonzero eigenvalue remove all arbitrary
integration constants. No radial profile is assumed. -/
theorem actual_circle_first_even_proportional (r : ℝ) (g : ℝ → ℝ)
    (hg : ContDiff ℝ 2 g) (hpos : ∀ t ∈ Icc (-1 : ℝ) 1,0<g t)
    (he : LatitudeEigenEquation 3 2 1 r (roundTiltMinimum 1 1 r (1/2)) g)
    (u : C^∞⟮𝓡 1,Circle;ℝ⟯) (hu : CircleEven u)
    (heig : ∀ x,weightedRoundApply (n := 1) circleAxis r u x=roundTiltMinimum 1 1 r (1/2)*u x) :
    ∃ c : ℝ,∀ x,u x=c*radialRecover 1 r (roundTiltMinimum 1 1 r (1/2)) g ((x : CircleAmbient) 0) := by
  have hlat := circle_even_constant_on_latitudes u hu
  obtain ⟨f,hf,hfu,hfe⟩ := actual_radial_candidate_C3_profile 0 r _ u hlat heig
  have hfe' : RadialEigenEquation 1 r (roundTiltMinimum 1 1 r (1/2)) f := hfe
  have hde := radial_eigenfunction_derivative_partner 1 r _ f hf hfe'
  obtain ⟨c,hc⟩ := original_weighted_eigenprofile_proportional 3 (by omega) 2 1 r _
    g (deriv f) hg hf.deriv' hpos he (by simpa only [Nat.cast_one] using hde)
  have hmu : roundTiltMinimum 1 1 r (1/2)≠0 := by
    exact (circle_first_minimum_pos r).ne'
  have hrec := radial_eigenprofile_recover_proportional 1 r _ c hmu f g hf hg hfe' hc
  refine ⟨c,?_⟩
  intro x
  have hfu' : u x=f ((x : CircleAmbient) 0) := by
    simpa [physicalCoordinate,innerCoordFun,EuclideanSpace.inner_single_left] using hfu x
  rw [hfu',hrec _ (circle_coord0_mem x)]

/-- The two original circle generators are linearly independent as
actual sphere functions. Their pole/equator values prove this directly. -/
theorem actual_circle_first_generators_independent (r : ℝ) (gO gE : ℝ → ℝ)
    (hpO : ∀ t ∈ Icc (-1 : ℝ) 1,0<gO t) (hpE : ∀ t ∈ Icc (-1 : ℝ) 1,0<gE t)
    (cE cO : ℝ)
    (hzero : ∀ x : Circle,cE*radialRecover 1 r (roundTiltMinimum 1 1 r (1/2)) gE ((x : CircleAmbient) 0)+
      cO*((x : CircleAmbient) 1*gO ((x : CircleAmbient) 0))=0) : cE=0 ∧ cO=0 := by
  let north : Circle := ⟨circleAxis,by simp [circleAxis]⟩
  let equator : Circle := ⟨circleTransverse,by simp [circleTransverse]⟩
  have hn := hzero north
  have he := hzero equator
  have hmu : roundTiltMinimum 1 1 r (1/2)≠0 := by
    exact (circle_first_minimum_pos r).ne'
  have hE : cE=0 := by
    norm_num [north,circleAxis,radialRecover,radialAdjoint] at hn
    exact hn.resolve_right (not_or.mpr ⟨(hpE 1 (by norm_num)).ne',hmu⟩)
  have hO : cO=0 := by
    rw [hE,zero_mul,zero_add] at he
    norm_num [equator,circleTransverse] at he
    exact he.resolve_right (hpO 0 (by norm_num)).ne'
  exact ⟨hE,hO⟩

/-- All actual smooth circle first eigenstates lie in the same two
original one-dimensional parity spans. The positive normalized auxiliary
profiles and the equality of their minima are proved, rather than supplied.
The two explicit actual sphere functions are linearly independent. -/
theorem actual_circle_first_eigenspace_span_exists (r : ℝ) :
    ∃ gO gE : ℝ → ℝ,
      ContDiff ℝ 2 gO ∧ (∀ t ∈ Icc (-1 : ℝ) 1,0<gO t) ∧ latitudeNorm 3 r gO=1 ∧
      LatitudeEigenEquation 3 1 1 r (roundTiltMinimum 1 1 r (1/2)) gO ∧
      ContDiff ℝ 2 gE ∧ (∀ t ∈ Icc (-1 : ℝ) 1,0<gE t) ∧ latitudeNorm 3 r gE=1 ∧
      LatitudeEigenEquation 3 2 1 r (roundTiltMinimum 1 1 r (1/2)) gE ∧
      (∀ u : C^∞⟮𝓡 1,Circle;ℝ⟯,
        (∀ x,weightedRoundApply (n := 1) circleAxis r u x=roundTiltMinimum 1 1 r (1/2)*u x) →
        ∃ cE cO : ℝ,∀ x,u x=
          cE*radialRecover 1 r (roundTiltMinimum 1 1 r (1/2)) gE ((x : CircleAmbient) 0)+
          cO*((x : CircleAmbient) 1*gO ((x : CircleAmbient) 0))) ∧
      (∀ cE cO : ℝ,
        (∀ x : Circle,cE*radialRecover 1 r (roundTiltMinimum 1 1 r (1/2)) gE ((x : CircleAmbient) 0)+
          cO*((x : CircleAmbient) 1*gO ((x : CircleAmbient) 0))=0) → cE=0 ∧ cO=0) := by
  obtain ⟨gO,hgO,hpO,hnO,heO⟩ := original_weighted_positive_ground_exists 3 (by omega) 1 1 r
  obtain ⟨gE,hgE,hpE,hnE,heE⟩ := original_weighted_positive_ground_exists 3 (by omega) 2 1 r
  have heO' : LatitudeEigenEquation 3 1 1 r (roundTiltMinimum 1 1 r (1/2)) gO := by
    norm_num at heO
    exact heO
  have heE' : LatitudeEigenEquation 3 2 1 r (roundTiltMinimum 1 1 r (1/2)) gE := by
    have hm := circle_radial_transverse_actual_ground_eq r
    norm_num at hm heE
    rw [hm] at heE
    exact heE
  refine ⟨gO,gE,hgO,hpO,hnO,heO',hgE,hpE,hnE,heE',?_,?_⟩
  · intro u hu
    have hpar := circle_parity_eigen r _ u hu
    obtain ⟨cE,hE⟩ := actual_circle_first_even_proportional r gE hgE hpE heE'
      (circleEvenPart u) (circle_evenPart_even u) hpar.1
    obtain ⟨cO,hO⟩ := actual_circle_first_odd_proportional r gO hgO hpO heO'
      (circleOddPart u) (circle_oddPart_odd u) hpar.2
    refine ⟨cE,cO,?_⟩
    intro x
    rw [← circle_even_odd_sum u x,hE x,hO x]
  · intro cE cO hz
    exact actual_circle_first_generators_independent r gO gE hpO hpE cE cO hz

end DFLCircleOdd
