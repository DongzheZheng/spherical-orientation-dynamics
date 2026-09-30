import continuation.PhysicalFirstEigenspace

/-! Exact dimension of the entire genuine smooth first eigenspace of
the physical weighted round-sphere operator. The subspace is defined by
actual smoothness and the actual PDE at the full-domain weighted gap. -/
noncomputable section
open Bundle Manifold Metric Module Set
open scoped Manifold ContDiff RealInnerProductSpace InnerProductSpace
open DFLSphere DFL.Spectral DFLTransverseSphere DFLWeightedSymmetry DFLPhysicalLatitude
namespace DFLPhysicalGap

/-- All genuine smooth first eigenfunctions of the original physical
operator, as a real subspace of functions on the actual sphere. -/
def physicalFirstSmoothSpace (k : ℕ) (r : ℝ) : Submodule ℝ (PhysicalSphere k → ℝ) where
  carrier := {f | ContMDiff (𝓡 (k+1)) 𝓘(ℝ,ℝ) ∞ f ∧
    ∀ x,weightedRoundApply (n := k+1) (EuclideanSpace.single 0 1) r f x=physicalGap k r*f x}
  zero_mem' := by
    refine ⟨contMDiff_const,?_⟩
    intro x
    let Z : C^∞⟮𝓡 (k+1),PhysicalSphere k;ℝ⟯ := ⟨fun _ => 0,contMDiff_const⟩
    have hh := weightedRoundApply_linear (EuclideanSpace.single 0 1) r 0 0 Z Z x
    change weightedRoundApply (n := k+1) (EuclideanSpace.single 0 1) r (fun _ => 0) x=physicalGap k r*0
    simpa only [zero_mul,mul_zero,zero_add] using hh
  add_mem' := by
    rintro f g ⟨hf,hef⟩ ⟨hg,heg⟩
    refine ⟨hf.add hg,?_⟩
    intro x
    let F : C^∞⟮𝓡 (k+1),PhysicalSphere k;ℝ⟯ := ⟨f,hf⟩
    let G : C^∞⟮𝓡 (k+1),PhysicalSphere k;ℝ⟯ := ⟨g,hg⟩
    have hh := weightedRoundApply_linear (EuclideanSpace.single 0 1) r 1 1 F G x
    simp only [one_mul] at hh
    change weightedRoundApply (n := k+1) (EuclideanSpace.single 0 1) r (fun y => f y+g y) x=
      weightedRoundApply (n := k+1) (EuclideanSpace.single 0 1) r f x+
      weightedRoundApply (n := k+1) (EuclideanSpace.single 0 1) r g x at hh
    rw [hef x,heg x] at hh
    exact hh.trans (by
      change physicalGap k r*f x+physicalGap k r*g x=physicalGap k r*(f x+g x)
      ring)
  smul_mem' := by
    rintro c f ⟨hf,hef⟩
    refine ⟨contMDiff_const.mul hf,?_⟩
    intro x
    let F : C^∞⟮𝓡 (k+1),PhysicalSphere k;ℝ⟯ := ⟨f,hf⟩
    let Z : C^∞⟮𝓡 (k+1),PhysicalSphere k;ℝ⟯ := ⟨fun _ => 0,contMDiff_const⟩
    have hh := weightedRoundApply_linear (EuclideanSpace.single 0 1) r c 0 F Z x
    simp only [zero_mul,add_zero] at hh
    change weightedRoundApply (n := k+1) (EuclideanSpace.single 0 1) r (fun y => c*f y) x=
      c*weightedRoundApply (n := k+1) (EuclideanSpace.single 0 1) r f x at hh
    rw [hef x] at hh
    exact hh.trans (by
      change c*(physicalGap k r*f x)=physicalGap k r*(c*f x)
      ring)

/-- At positive field in physical dimensions at least two, the entire
actual smooth first eigenspace is exactly the range of transverse amplitudes
with one actual positive latitude ground profile. -/
theorem actual_physical_first_smooth_space_eq_transverse_exists
    (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r) :
    ∃v : ℝ → ℝ,ContDiff ℝ 2 v ∧ (∀t∈Icc (-1 : ℝ) 1,0<v t) ∧
      latitudeNorm (k+3) r v=1 ∧
      LatitudeEigenEquation (k+3) 1 ((k+1 : ℕ) : ℝ) r
        (roundTiltMinimum (k+1) ((k+1 : ℕ) : ℝ) r (((k+1 : ℕ) : ℝ)/2)) v ∧
      physicalFirstSmoothSpace k r=
        transverseMode_range (EuclideanSpace.single 0 1 : PhysicalAmbient k) v := by
  obtain ⟨v,hv,hpos,hN,heig,hSmooth,hiff,_hUnique,_hRank⟩ :=
    actual_first_eigenspace_common_ground_exists k hk r hr
  refine ⟨v,hv,hpos,hN,heig,?_⟩
  apply Submodule.ext
  intro f
  rw [mem_transverseMode_range_iff]
  constructor
  · rintro ⟨hf,hef⟩
    let F : C^∞⟮𝓡 (k+1),PhysicalSphere k;ℝ⟯ := ⟨f,hf⟩
    obtain ⟨a,ha,hrep⟩ := (hiff F).mp hef
    exact ⟨a,ha,funext hrep⟩
  · rintro ⟨a,ha,rfl⟩
    refine ⟨hSmooth a,?_⟩
    let F : C^∞⟮𝓡 (k+1),PhysicalSphere k;ℝ⟯ :=
      ⟨transverseMode (EuclideanSpace.single 0 1) a v,hSmooth a⟩
    exact (hiff F).mpr ⟨a,ha,fun _ => rfl⟩

/-- The entire genuine smooth first eigenspace, defined directly by the
original physical PDE at its actual full-domain weighted gap, has exact
real dimension equal to the physical sphere dimension k+1. -/
theorem actual_physical_first_smooth_space_finrank
    (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r) :
    finrank ℝ (physicalFirstSmoothSpace k r)=k+1 := by
  obtain ⟨v,_hv,hpos,_hN,_heig,hSpace⟩ :=
    actual_physical_first_smooth_space_eq_transverse_exists k hk r hr
  rw [hSpace]
  exact transverseMode_range_finrank (n := k+1)
    (EuclideanSpace.single 0 1 : PhysicalAmbient k) (by simp) v hpos

end DFLPhysicalGap
