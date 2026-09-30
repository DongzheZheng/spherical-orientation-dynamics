import DFL.Spectral.ClosedFormGap
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Linear and Hilbert structure of the physical smooth graph completion

The pairs are still those of the original weighted sphere: a centered
value and its actual tangent gradient.  This file proves that their smooth
range is a linear subspace and that its closure is a closed linear subspace.
Changing the product norm to the `L²` product gives a genuine complete
inner-product form domain, with norm squared exactly variance plus energy.

This does not assert gradient closability or identification with classical
weak-gradient `H¹`.  Those are separate statements about the value projection.
-/

namespace DFL.Spectral

open MeasureTheory InnerProductSpace

noncomputable section

def zeroCore (d : ℕ) : SphereC1Core d :=
  ⟨fun _ => 0, contDiff_const⟩

def addCore (d : ℕ) (f g : SphereC1Core d) : SphereC1Core d :=
  ⟨fun x => f.toFun x + g.toFun x, f.smooth.add g.smooth⟩

def scaleCore (d : ℕ) (a : ℝ) (f : SphereC1Core d) : SphereC1Core d :=
  ⟨fun x => a • f.toFun x, f.smooth.const_smul a⟩

@[simp] theorem coreValue_zero (d : ℕ) :
    coreValue d (zeroCore d) = 0 := rfl

@[simp] theorem coreValue_add (d : ℕ) (f g : SphereC1Core d) :
    coreValue d (addCore d f g) = coreValue d f + coreValue d g := rfl

@[simp] theorem coreValue_scale (d : ℕ) (a : ℝ) (f : SphereC1Core d) :
    coreValue d (scaleCore d a f) = a • coreValue d f := rfl

@[simp] theorem coreTangentGradient_zero (d : ℕ) :
    coreTangentGradient d (zeroCore d) = 0 := by
  funext x
  simp [coreTangentGradient, zeroCore, gradient_fun_const]

@[simp] theorem coreTangentGradient_add (d : ℕ) (f g : SphereC1Core d) :
    coreTangentGradient d (addCore d f g) =
      coreTangentGradient d f + coreTangentGradient d g := by
  have hf : Differentiable ℝ f.toFun := f.smooth.differentiable (by norm_num)
  have hg : Differentiable ℝ g.toFun := g.smooth.differentiable (by norm_num)
  funext x
  have hgrad : gradient (addCore d f g).toFun x.1 =
      gradient f.toFun x.1 + gradient g.toFun x.1 := by
    simp only [addCore, gradient, fderiv_fun_add (hf x.1) (hg x.1), map_add]
  simp only [Pi.add_apply, coreTangentGradient, hgrad, inner_add_left, add_smul]
  abel

@[simp] theorem coreTangentGradient_scale (d : ℕ) (a : ℝ)
    (f : SphereC1Core d) :
    coreTangentGradient d (scaleCore d a f) = a • coreTangentGradient d f := by
  have hf : Differentiable ℝ f.toFun := f.smooth.differentiable (by norm_num)
  funext x
  have hgrad : gradient (scaleCore d a f).toFun x.1 =
      a • gradient f.toFun x.1 := by
    simp only [scaleCore, gradient, fderiv_fun_const_smul (hf x.1), map_smul]
  simp only [coreTangentGradient, hgrad, real_inner_smul_left,
    smul_sub, smul_smul, Pi.smul_apply]

@[simp] theorem centeredCoreValue_zero (d : ℕ) (r : ℝ) :
    centeredCoreValue d r (zeroCore d) = 0 := by
  funext x
  simp [centeredCoreValue]

@[simp] theorem centeredCoreValue_add (d : ℕ) (r : ℝ)
    (f g : SphereC1Core d) :
    centeredCoreValue d r (addCore d f g) =
      centeredCoreValue d r f + centeredCoreValue d r g := by
  letI : IsProbabilityMeasure (alignedMeasure d r) := alignedMeasure_probability d r
  have hf := (coreValue_memLp d r f).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hg := (coreValue_memLp d r g).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  funext x
  simp only [centeredCoreValue, coreValue_add, Pi.add_apply, integral_add hf hg]
  ring

@[simp] theorem centeredCoreValue_scale (d : ℕ) (r a : ℝ)
    (f : SphereC1Core d) :
    centeredCoreValue d r (scaleCore d a f) = a • centeredCoreValue d r f := by
  funext x
  simp only [centeredCoreValue, coreValue_scale, Pi.smul_apply,
    smul_eq_mul, integral_const_mul]
  ring

@[simp] theorem coreGraph_zero (d : ℕ) (r : ℝ) :
    coreGraph d r (zeroCore d) = 0 := by
  simp [coreGraph]

@[simp] theorem coreGraph_add (d : ℕ) (r : ℝ) (f g : SphereC1Core d) :
    coreGraph d r (addCore d f g) = coreGraph d r f + coreGraph d r g := by
  apply Prod.ext
  all_goals simp only [Prod.fst_add, Prod.snd_add, coreGraph]
  · change (centeredCoreValue_memLp d r (addCore d f g)).toLp _ = _
    rw [← MemLp.toLp_add (centeredCoreValue_memLp d r f)
      (centeredCoreValue_memLp d r g)]
    exact MemLp.toLp_congr _ _ (ae_of_all _ (fun x => congrFun (centeredCoreValue_add d r f g) x))
  · change (coreTangentGradient_memLp d r (addCore d f g)).toLp _ = _
    rw [← MemLp.toLp_add (coreTangentGradient_memLp d r f)
      (coreTangentGradient_memLp d r g)]
    exact MemLp.toLp_congr _ _ (ae_of_all _ (fun x => congrFun (coreTangentGradient_add d f g) x))

@[simp] theorem coreGraph_scale (d : ℕ) (r a : ℝ) (f : SphereC1Core d) :
    coreGraph d r (scaleCore d a f) = a • coreGraph d r f := by
  apply Prod.ext
  all_goals simp only [Prod.smul_fst, Prod.smul_snd, coreGraph]
  · change (centeredCoreValue_memLp d r (scaleCore d a f)).toLp _ = _
    rw [← MemLp.toLp_const_smul a (centeredCoreValue_memLp d r f)]
    exact MemLp.toLp_congr _ _ (ae_of_all _ (fun x => congrFun (centeredCoreValue_scale d r a f) x))
  · change (coreTangentGradient_memLp d r (scaleCore d a f)).toLp _ = _
    rw [← MemLp.toLp_const_smul a (coreTangentGradient_memLp d r f)]
    exact MemLp.toLp_congr _ _ (ae_of_all _ (fun x => congrFun (coreTangentGradient_scale d a f) x))

/-- The exact smooth centered value/tangent-gradient graph is a submodule. -/
def smoothGraphSubmodule (d : ℕ) (r : ℝ) :
    Submodule ℝ (Lp ℝ 2 (alignedMeasure d r) ×
      Lp (Ambient d) 2 (alignedMeasure d r)) where
  carrier := Set.range (coreGraph d r)
  zero_mem' := ⟨zeroCore d, coreGraph_zero d r⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨addCore d f g, coreGraph_add d r f g⟩
  smul_mem' := by
    rintro a _ ⟨f, rfl⟩
    exact ⟨scaleCore d a f, coreGraph_scale d r a f⟩

/-- The old metric graph closure has the complete linear subspace structure. -/
def closedGraphSubmodule (d : ℕ) (r : ℝ) :=
  (smoothGraphSubmodule d r).topologicalClosure

theorem closedGraphSubmodule_coe (d : ℕ) (r : ℝ) :
    (closedGraphSubmodule d r : Set (Lp ℝ 2 (alignedMeasure d r) ×
      Lp (Ambient d) 2 (alignedMeasure d r))) = closedFormGraph d r := rfl

theorem closedGraphSubmodule_isClosed (d : ℕ) (r : ℝ) :
    IsClosed (closedGraphSubmodule d r : Set (Lp ℝ 2 (alignedMeasure d r) ×
      Lp (Ambient d) 2 (alignedMeasure d r))) :=
  (smoothGraphSubmodule d r).isClosed_topologicalClosure

/-- The value/gradient product with the physically natural sum-of-squares norm. -/
abbrev HilbertFormPair (d : ℕ) (r : ℝ) :=
  WithLp 2 (Lp ℝ 2 (alignedMeasure d r) ×
    Lp (Ambient d) 2 (alignedMeasure d r))

/-- The same completed graph in the equivalent Hilbert product topology. -/
def hilbertFormSubmodule (d : ℕ) (r : ℝ) : Submodule ℝ (HilbertFormPair d r) :=
  (closedGraphSubmodule d r).comap
    (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toLinearMap

theorem hilbertFormSubmodule_isClosed (d : ℕ) (r : ℝ) :
    IsClosed (hilbertFormSubmodule d r : Set (HilbertFormPair d r)) :=
  (closedGraphSubmodule_isClosed d r).preimage
    (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).continuous

/-- The full smooth graph completion is a real Hilbert space. -/
abbrev HilbertFormSpace (d : ℕ) (r : ℝ) := hilbertFormSubmodule d r

instance hilbertFormSpace_complete (d : ℕ) (r : ℝ) :
    CompleteSpace (HilbertFormSpace d r) :=
  (hilbertFormSubmodule_isClosed d r).completeSpace_coe

def coreToHilbert (d : ℕ) (r : ℝ) (f : SphereC1Core d) : HilbertFormSpace d r :=
  ⟨WithLp.toLp 2 (coreGraph d r f), subset_closure ⟨f, rfl⟩⟩

/-- The Hilbert graph norm has exactly the original variance and energy. -/
theorem coreToHilbert_norm_sq (d : ℕ) (r : ℝ) (f : SphereC1Core d) :
    ‖coreToHilbert d r f‖ ^ 2 =
      sphereVariance d r (coreValue d f) + coreEnergy d r f := by
  change ‖WithLp.toLp 2 (coreGraph d r f)‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  exact congrArg₂ (· + ·) (coreGraph_value_norm_sq d r f)
    (coreGraph_gradient_norm_sq d r f)

end

end DFL.Spectral
