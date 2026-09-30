import continuation.CircleFirstSmoothBasis
import continuation.CircleGapEquality
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Exact real dimension of the genuine smooth first eigenspace of the
original weighted circle operator, at the actual full-domain weighted gap. -/
noncomputable section
open Set Metric Module Bundle Manifold
open scoped Manifold ContDiff RealInnerProductSpace InnerProductSpace
open DFLTransverseSphere DFLWeightedSymmetry DFLPhysicalGap DFLSphere
namespace DFLCircleOdd

/-- Actual smooth first eigenfunctions form a real linear subspace of
real functions on the genuine physical circle. -/
def circleFirstSmoothSpace (r : ℝ) : Submodule ℝ (Circle → ℝ) where
  carrier := {f | ContMDiff (𝓡 1) 𝓘(ℝ,ℝ) ∞ f ∧
    ∀ x,weightedRoundApply (n := 1) circleAxis r f x=weightedGap (n := 1) circleAxis r*f x}
  zero_mem' := by
    refine ⟨contMDiff_const,?_⟩
    intro x
    let Z : C^∞⟮𝓡 1,Circle;ℝ⟯ := ⟨fun _ => 0,contMDiff_const⟩
    have hh := weightedRoundApply_linear circleAxis r 0 0 Z Z x
    change weightedRoundApply (n := 1) circleAxis r (fun _ => 0) x=weightedGap (n := 1) circleAxis r*0
    simpa only [zero_mul,mul_zero,zero_add] using hh
  add_mem' := by
    rintro f g ⟨hf,hef⟩ ⟨hg,heg⟩
    refine ⟨hf.add hg,?_⟩
    intro x
    let F : C^∞⟮𝓡 1,Circle;ℝ⟯ := ⟨f,hf⟩
    let G : C^∞⟮𝓡 1,Circle;ℝ⟯ := ⟨g,hg⟩
    have hh := weightedRoundApply_linear circleAxis r 1 1 F G x
    simp only [one_mul] at hh
    change weightedRoundApply (n := 1) circleAxis r (fun y => f y+g y) x=
      weightedRoundApply (n := 1) circleAxis r f x+weightedRoundApply (n := 1) circleAxis r g x at hh
    rw [hef x,heg x] at hh
    exact hh.trans (by
      change weightedGap (n := 1) circleAxis r*f x+
        weightedGap (n := 1) circleAxis r*g x=weightedGap (n := 1) circleAxis r*(f x+g x)
      ring)
  smul_mem' := by
    rintro c f ⟨hf,hef⟩
    refine ⟨contMDiff_const.mul hf,?_⟩
    intro x
    let F : C^∞⟮𝓡 1,Circle;ℝ⟯ := ⟨f,hf⟩
    let Z : C^∞⟮𝓡 1,Circle;ℝ⟯ := ⟨fun _ => 0,contMDiff_const⟩
    have hh := weightedRoundApply_linear circleAxis r c 0 F Z x
    simp only [zero_mul,add_zero] at hh
    change weightedRoundApply (n := 1) circleAxis r (fun y => c*f y) x=
      c*weightedRoundApply (n := 1) circleAxis r f x at hh
    rw [hef x] at hh
    exact hh.trans (by
      change c*(weightedGap (n := 1) circleAxis r*f x)=
        weightedGap (n := 1) circleAxis r*(c*f x)
      ring)

private def pairAmplitudeMap (E O : Circle → ℝ) : (ℝ×ℝ) →ₗ[ℝ] (Circle → ℝ) where
  toFun a := fun x => a.1*E x+a.2*O x
  map_add' a b := by
    funext x
    change (a.1+b.1)*E x+(a.2+b.2)*O x=(a.1*E x+a.2*O x)+(b.1*E x+b.2*O x)
    ring
  map_smul' c a := by
    funext x
    change (c*a.1)*E x+(c*a.2)*O x=(RingHom.id ℝ c)*(a.1*E x+a.2*O x)
    rw [RingHom.id_apply]
    ring

/-- The actual smooth circle first eigenspace has exact real dimension
two for every real field, including zero. The independent smooth basis,
true operator equations and full-space gap equality are all proved. -/
theorem actual_circle_first_smooth_space_finrank (r : ℝ) :
    finrank ℝ (circleFirstSmoothSpace r)=2 := by
  obtain ⟨E,O,_hEven,_hOdd,_hEn,_hOn,heE,heO,hiff,hunique⟩ :=
    actual_circle_first_smooth_basis_exists r
  have hgap := actual_circle_gap_eq_transverse r
  rw [← hgap] at heE heO hiff
  let L := pairAmplitudeMap (E : Circle → ℝ) (O : Circle → ℝ)
  have hinj : Function.Injective L := by
    intro a b hab
    have hh := hunique a.1 a.2 b.1 b.2 (fun x => congrArg (fun f : Circle → ℝ => f x) hab)
    exact Prod.ext hh.1 hh.2
  have hR : L.range=circleFirstSmoothSpace r := by
    apply Submodule.ext
    intro f
    constructor
    · rintro ⟨c,rfl⟩
      refine ⟨(contMDiff_const.mul E.contMDiff).add (contMDiff_const.mul O.contMDiff),?_⟩
      intro x
      change weightedRoundApply (n := 1) circleAxis r (fun y => c.1*E y+c.2*O y) x=_
      rw [weightedRoundApply_linear circleAxis r c.1 c.2 E O x,heE,heO]
      change c.1*(weightedGap (n := 1) circleAxis r*E x)+
        c.2*(weightedGap (n := 1) circleAxis r*O x)=
          weightedGap (n := 1) circleAxis r*(c.1*E x+c.2*O x)
      ring
    · rintro ⟨hf,hef⟩
      let F : C^∞⟮𝓡 1,Circle;ℝ⟯ := ⟨f,hf⟩
      obtain ⟨cE,cO,hc⟩ := (hiff F).mp hef
      exact ⟨(cE,cO),funext (fun x => (hc x).symm)⟩
  calc
    _=finrank ℝ L.range := by rw [hR]
    _=finrank ℝ (ℝ×ℝ) := LinearMap.finrank_range_of_inj hinj
    _=2 := by simp only [Module.finrank_prod,Module.finrank_self]

end DFLCircleOdd
