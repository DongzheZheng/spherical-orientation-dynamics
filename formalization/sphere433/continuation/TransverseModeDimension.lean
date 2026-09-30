import continuation.TransverseSphereMode
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Actual whole-sphere transverse amplitudes are unique. The linear
space of modes with one common positive latitude profile is the genuine
linear image of the axis orthogonal complement and has its exact dimension.
This is finite-dimensional linear algebra on actual sphere functions,
without a spectral-classification assumption. -/
noncomputable section
open Set Metric Module
open scoped RealInnerProductSpace InnerProductSpace
namespace DFLTransverseSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Whole-sphere equality of two common-positive-profile modes uniquely
determines their actual ambient amplitudes. No perpendicularity of those
two amplitudes is needed for injectivity. -/
theorem transverseMode_amplitude_injective (p : E) (hp : ‖p‖=1) (v : ℝ → ℝ)
    (hpos : ∀ t ∈ Icc (-1 : ℝ) 1,0<v t) :
    Function.Injective (fun a : E => transverseMode p a v) := by
  intro a b hab
  by_contra hne
  let d := a-b
  have hd : d≠0 := sub_ne_zero.mpr hne
  have hn : 0<‖d‖ := norm_pos_iff.mpr hd
  let x : sphere (0 : E) 1 := ⟨‖d‖⁻¹ • d,by
    rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ hn.ne']⟩
  have hb := abs_real_inner_le_norm p (x : E)
  rw [hp,norm_eq_of_mem_sphere x,mul_one] at hb
  have hv := (hpos _ (abs_le.mp hb)).ne'
  have hh := congrArg (fun f : sphere (0 : E) 1 → ℝ => f x) hab
  change ⟪a,(x : E)⟫_ℝ *v ⟪p,(x : E)⟫_ℝ=⟪b,(x : E)⟫_ℝ *v ⟪p,(x : E)⟫_ℝ at hh
  have hi : ⟪a,(x : E)⟫_ℝ=⟪b,(x : E)⟫_ℝ := mul_right_cancel₀ hv hh
  have hz : ⟪d,(x : E)⟫_ℝ=0 := by
    change ⟪a-b,(x : E)⟫_ℝ=0
    rw [inner_sub_left,hi,sub_self]
  change ⟪d,‖d‖⁻¹ • d⟫_ℝ=0 at hz
  rw [real_inner_smul_right,real_inner_self_eq_norm_sq] at hz
  exact (mul_pos (inv_pos.mpr hn) (sq_pos_of_pos hn)).ne' hz

/-- Actual transverse amplitude map from the true axis orthogonal
complement into real functions on the actual unit sphere. -/
def transverseAmplitudeMap (p : E) (v : ℝ → ℝ) :
    (ℝ ∙ p)ᗮ →ₗ[ℝ] (sphere (0 : E) 1 → ℝ) where
  toFun a := transverseMode p (a : E) v
  map_add' a b := by
    funext x
    simp only [transverseMode,Submodule.coe_add,inner_add_left,Pi.add_apply]
    ring
  map_smul' c a := by
    funext x
    simp only [transverseMode,Submodule.coe_smul,real_inner_smul_left,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

/-- The actual common-profile transverse mode subspace. -/
def transverseMode_range (p : E) (v : ℝ → ℝ) : Submodule ℝ (sphere (0 : E) 1 → ℝ) :=
  (transverseAmplitudeMap p v).range

/-- Membership is exactly realizability by one actual orthogonal
ambient amplitude, with the original whole-sphere mode formula. -/
theorem mem_transverseMode_range_iff (p : E) (v : ℝ → ℝ) (f : sphere (0 : E) 1 → ℝ) :
    f∈transverseMode_range p v ↔ ∃ a : E,⟪a,p⟫_ℝ=0 ∧ f=transverseMode p a v := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,Submodule.mem_orthogonal_singleton_iff_inner_left.mp a.property,ha.symm⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨a,Submodule.mem_orthogonal_singleton_iff_inner_left.mpr ha⟩,rfl⟩

/-- The actual amplitude map is injective when the shared profile is
positive on the physical interval. -/
theorem transverseAmplitudeMap_injective (p : E) (hp : ‖p‖=1) (v : ℝ → ℝ)
    (hpos : ∀ t ∈ Icc (-1 : ℝ) 1,0<v t) :
    Function.Injective (transverseAmplitudeMap p v) := by
  intro a b hab
  apply Subtype.ext
  exact transverseMode_amplitude_injective p hp v hpos hab

/-- A genuine linear equivalence identifies the mode range with the
actual axis orthogonal complement. -/
def transverseAmplitudeEquivRange (p : E) (hp : ‖p‖=1) (v : ℝ → ℝ)
    (hpos : ∀ t ∈ Icc (-1 : ℝ) 1,0<v t) :
    (ℝ ∙ p)ᗮ ≃ₗ[ℝ] transverseMode_range p v :=
  LinearEquiv.ofInjective (transverseAmplitudeMap p v) (transverseAmplitudeMap_injective p hp v hpos)

/-- In an actual ambient space of dimension n+1, the common-positive-
profile transverse mode range has exact real dimension n. The result
also covers n=0 as a purely geometric linear-algebra endpoint. -/
theorem transverseMode_range_finrank (n : ℕ) [Fact (finrank ℝ E=n+1)]
    (p : E) (hp : ‖p‖=1) (v : ℝ → ℝ)
    (hpos : ∀ t ∈ Icc (-1 : ℝ) 1,0<v t) :
    finrank ℝ (transverseMode_range p v)=n := by
  have hpne : p≠0 := by intro h;rw [h,norm_zero] at hp;norm_num at hp
  calc
    _=finrank ℝ (ℝ ∙ p)ᗮ :=
      LinearMap.finrank_range_of_inj (transverseAmplitudeMap_injective p hp v hpos)
    _=n := Submodule.finrank_orthogonal_span_singleton hpne

end DFLTransverseSphere
