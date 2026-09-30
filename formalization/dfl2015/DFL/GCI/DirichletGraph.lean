import DFL.GCI.IntegralPrimitiveL2

/-! A complete graph realization of the *original* singular angular
Dirichlet domain. Its coordinates are the weighted representative's true
derivative `q=u′` and its singular mass coordinate `y=u/sin θ`.
Unlike a completion of unrelated smooth profiles, the graph enforces the
primitive identity and the two Dirichlet traces directly. -/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

theorem l2_mul_memLp (f : ℝ → ℝ) (hf : AEStronglyMeasurable f angularLebesgue)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ θ ∂angularLebesgue, ‖f θ‖ ≤ C)
    (q : AngularL2) : MemLp (fun θ => f θ * q θ) 2 angularLebesgue := by
  have _ := hC
  apply (Lp.memLp q).of_le_mul (c := C) (hf.mul (Lp.aestronglyMeasurable q))
  filter_upwards [hb] with θ hθ
  simpa only [Pi.mul_apply, norm_mul] using mul_le_mul_of_nonneg_right hθ (norm_nonneg (q θ))

def l2MulLinear (f : ℝ → ℝ) (hf : AEStronglyMeasurable f angularLebesgue)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ θ ∂angularLebesgue, ‖f θ‖ ≤ C) :
    AngularL2 →ₗ[ℝ] AngularL2 where
  toFun q := (l2_mul_memLp f hf C hC hb q).toLp (fun θ => f θ * q θ)
  map_add' q t := by
    apply Lp.ext
    filter_upwards [(l2_mul_memLp f hf C hC hb (q+t)).coeFn_toLp,
      (l2_mul_memLp f hf C hC hb q).coeFn_toLp,
      (l2_mul_memLp f hf C hC hb t).coeFn_toLp,
      Lp.coeFn_add q t,
      Lp.coeFn_add ((l2_mul_memLp f hf C hC hb q).toLp _)
        ((l2_mul_memLp f hf C hC hb t).toLp _)] with θ hleft hq ht hsum hright
    simp only [hleft, hright, Pi.add_apply, hq, ht, hsum]
    ring
  map_smul' a q := by
    apply Lp.ext
    filter_upwards [(l2_mul_memLp f hf C hC hb (a•q)).coeFn_toLp,
      (l2_mul_memLp f hf C hC hb q).coeFn_toLp,
      Lp.coeFn_smul a q,
      Lp.coeFn_smul a ((l2_mul_memLp f hf C hC hb q).toLp _)]
      with θ hleft hq hsum hright
    simp only [RingHom.id_apply, hleft, hright, Pi.smul_apply,
      smul_eq_mul, hq, hsum]
    ring

theorem l2MulLinear_bound (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f angularLebesgue)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ θ ∂angularLebesgue, ‖f θ‖ ≤ C)
    (q : AngularL2) : ‖l2MulLinear f hf C hC hb q‖ ≤ C * ‖q‖ := by
  calc
    ‖l2MulLinear f hf C hC hb q‖ ≤ ‖C • q‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [(l2_mul_memLp f hf C hC hb q).coeFn_toLp,
        Lp.coeFn_smul C q, hb] with θ hleft hright hθ
      change ‖(((l2_mul_memLp f hf C hC hb q).toLp _) : ℝ → ℝ) θ‖ ≤ _
      rw [hleft, hright]
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right hθ (norm_nonneg (q θ))
    _ = C * ‖q‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]

def l2MulCLM (f : ℝ → ℝ) (hf : AEStronglyMeasurable f angularLebesgue)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ θ ∂angularLebesgue, ‖f θ‖ ≤ C) :
    AngularL2 →L[ℝ] AngularL2 :=
  (l2MulLinear f hf C hC hb).mkContinuous C (l2MulLinear_bound f hf C hC hb)

theorem l2MulCLM_ae (f : ℝ → ℝ) (hf : AEStronglyMeasurable f angularLebesgue)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ θ ∂angularLebesgue, ‖f θ‖ ≤ C)
    (q : AngularL2) :
    (l2MulCLM f hf C hC hb q : ℝ → ℝ) =ᵐ[angularLebesgue] fun θ => f θ * q θ :=
  (l2_mul_memLp f hf C hC hb q).coeFn_toLp

def sineMultiplier : AngularL2 →L[ℝ] AngularL2 :=
  l2MulCLM Real.sin Real.continuous_sin.aestronglyMeasurable 1 (by norm_num)
    (ae_of_all _ (by intro θ; simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one θ))

def cosineMultiplier : AngularL2 →L[ℝ] AngularL2 :=
  l2MulCLM Real.cos Real.continuous_cos.aestronglyMeasurable 1 (by norm_num)
    (ae_of_all _ (by intro θ; simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one θ))

abbrev AngularGraphAmbient := WithLp 2 (AngularL2 × AngularL2)

def graphDerivative : AngularGraphAmbient →L[ℝ] AngularL2 :=
  WithLp.fstL 2 ℝ AngularL2 AngularL2

def graphSingular : AngularGraphAmbient →L[ℝ] AngularL2 :=
  WithLp.sndL 2 ℝ AngularL2 AngularL2

def graphConstraint : AngularGraphAmbient →L[ℝ] AngularL2 :=
  sineMultiplier.comp graphSingular - l2PrimitiveCLM.comp graphDerivative

def graphTrace : AngularGraphAmbient →L[ℝ] ℝ :=
  (innerSL ℝ ((Lp.const 2 angularLebesgue) (1 : ℝ))).comp graphDerivative

/-- `q=u′`, `u=sin θ*y`, and `u(π)=u(0)=0`. The zero trace at 0
is inherent in the primitive; the remaining trace is `graphTrace=0`. -/
def dirichletGraph : Submodule ℝ AngularGraphAmbient :=
  graphConstraint.ker ⊓ graphTrace.ker

theorem dirichletGraph_isClosed : IsClosed (dirichletGraph : Set AngularGraphAmbient) :=
  graphConstraint.isClosed_ker.inter graphTrace.isClosed_ker

instance : CompleteSpace dirichletGraph :=
  dirichletGraph_isClosed.completeSpace_coe

theorem dirichletGraph_primitive_ae (p : dirichletGraph) :
    (fun θ => Real.sin θ * (graphSingular p) θ) =ᵐ[angularLebesgue]
      l2Primitive (graphDerivative p) := by
  have h : sineMultiplier (graphSingular p) = l2PrimitiveCLM (graphDerivative p) := by
    have hp := p.property.1
    change graphConstraint p = 0 at hp
    exact sub_eq_zero.mp hp
  have hs := l2MulCLM_ae Real.sin Real.continuous_sin.aestronglyMeasurable 1
    (by norm_num)
    (ae_of_all _ (by intro θ; simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one θ))
    (graphSingular p)
  exact hs.symm.trans ((Lp.ext_iff.mp h).trans (l2PrimitiveCLM_ae (graphDerivative p)))

theorem dirichletGraph_zero_trace (p : dirichletGraph) :
    l2Primitive (graphDerivative p) Real.pi = 0 := by
  have hp := p.property.2
  change inner ℝ ((Lp.const 2 angularLebesgue) (1 : ℝ)) (graphDerivative p) = 0 at hp
  have hconst := Lp.coeFn_const 2 angularLebesgue (1 : ℝ)
  have heq : inner ℝ ((Lp.const 2 angularLebesgue) (1 : ℝ)) (graphDerivative p) =
      ∫ θ, (graphDerivative p) θ ∂angularLebesgue := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hconst] with θ hθ
    rw [hθ]
    simp only [Function.const_apply]
    rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
    simp
  rw [heq] at hp
  simpa [l2Primitive, angularLebesgue, Measure.restrict_restrict] using hp

end
end DFL.GCI
