import DFL.GCI.DirichletGraph

/-! Existence in the exact closed Dirichlet graph by Lax--Milgram.
The energy transformation retains both original mass and derivative
coordinates. Its inverse proves coercivity without a Hardy estimate. -/

namespace DFL.GCI

open MeasureTheory

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem graphWeight_bound (r θ : ℝ) :
    ‖Real.exp (r * Real.cos θ / 2)‖ ≤ Real.exp (|r| / 2) := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hc := Real.abs_cos_le_one θ
  have h : r * Real.cos θ ≤ |r| := by
    calc
      _ ≤ |r * Real.cos θ| := le_abs_self _
      _ = |r| * |Real.cos θ| := abs_mul _ _
      _ ≤ |r| * 1 := mul_le_mul_of_nonneg_left hc (abs_nonneg _)
      _ = |r| := mul_one _
  linarith

def graphWeight (r : ℝ) : AngularL2 →L[ℝ] AngularL2 :=
  l2MulCLM (fun θ => Real.exp (r * Real.cos θ / 2))
    (by fun_prop) (Real.exp (|r| / 2)) (Real.exp_nonneg _)
    (ae_of_all _ (graphWeight_bound r))

theorem graphWeight_ae (r : ℝ) (q : AngularL2) :
    (graphWeight r q : ℝ → ℝ) =ᵐ[angularLebesgue]
      (fun θ => Real.exp (r * Real.cos θ / 2) * q θ) :=
  l2MulCLM_ae _ _ _ _ _ q

theorem graphWeight_inverse (r : ℝ) (q : AngularL2) :
    graphWeight (-r) (graphWeight r q) = q := by
  apply Lp.ext
  filter_upwards [graphWeight_ae (-r) (graphWeight r q), graphWeight_ae r q]
    with θ hleft hright
  rw [hleft, hright, ← mul_assoc, ← Real.exp_add]
  rw [show (-r) * Real.cos θ / 2 + r * Real.cos θ / 2 = 0 by ring]
  simp

def graphPair (f g : AngularGraphAmbient →L[ℝ] AngularL2) :
    AngularGraphAmbient →L[ℝ] AngularGraphAmbient :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ AngularL2 AngularL2).symm.toContinuousLinearMap.comp
    (f.prod g)

@[simp] theorem graphPair_fst (f g : AngularGraphAmbient →L[ℝ] AngularL2)
    (x : AngularGraphAmbient) : graphDerivative (graphPair f g x) = f x := rfl

@[simp] theorem graphPair_snd (f g : AngularGraphAmbient →L[ℝ] AngularL2)
    (x : AngularGraphAmbient) : graphSingular (graphPair f g x) = g x := rfl

def graphEnergyTransform (n : ℕ) (r : ℝ) :
    AngularGraphAmbient →L[ℝ] AngularGraphAmbient :=
  graphPair
    ((graphWeight r).comp (graphDerivative - halfPower n • cosineMultiplier.comp graphSingular))
    (Real.sqrt ((n : ℝ) - 2) • (graphWeight r).comp graphSingular)

def graphEnergyInverse (n : ℕ) (r : ℝ) :
    AngularGraphAmbient →L[ℝ] AngularGraphAmbient :=
  let y := (Real.sqrt ((n : ℝ) - 2))⁻¹ • (graphWeight (-r)).comp graphSingular
  graphPair ((graphWeight (-r)).comp graphDerivative + halfPower n • cosineMultiplier.comp y) y

theorem graphEnergyInverse_left (n : ℕ) (hn : 3 ≤ n) (r : ℝ)
    (x : AngularGraphAmbient) :
    graphEnergyInverse n r (graphEnergyTransform n r x) = x := by
  have hb : Real.sqrt ((n : ℝ) - 2) ≠ 0 := by
    apply (Real.sqrt_pos.mpr ?_).ne'
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hy : graphSingular (graphEnergyInverse n r (graphEnergyTransform n r x)) =
      graphSingular x := by
    simp only [graphEnergyInverse, graphPair_snd, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, graphEnergyTransform]
    rw [map_smul, graphWeight_inverse, smul_smul, inv_mul_cancel₀ hb, one_smul]
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ AngularL2 AngularL2).injective
  apply Prod.ext
  · change graphDerivative (graphEnergyInverse n r (graphEnergyTransform n r x)) =
      graphDerivative x
    simp only [graphEnergyInverse, graphPair_fst, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
    change graphWeight (-r) (graphDerivative (graphEnergyTransform n r x)) +
      halfPower n • cosineMultiplier (graphSingular (graphEnergyInverse n r
        (graphEnergyTransform n r x))) = _
    rw [hy]
    simp [graphEnergyTransform, graphWeight_inverse]
  · exact hy

def graphEnergyMap (n : ℕ) (r : ℝ) :
    dirichletGraph →L[ℝ] AngularGraphAmbient :=
  (graphEnergyTransform n r).comp dirichletGraph.subtypeL

def graphEnergyBilinear (n : ℕ) (r : ℝ) :
    dirichletGraph →L[ℝ] dirichletGraph →L[ℝ] ℝ :=
  ((graphEnergyMap n r).precomp ℝ).comp ((innerSL ℝ).comp (graphEnergyMap n r))

@[simp] theorem graphEnergyBilinear_apply (n : ℕ) (r : ℝ)
    (x y : dirichletGraph) :
    graphEnergyBilinear n r x y =
      inner ℝ (graphEnergyMap n r x) (graphEnergyMap n r y) := rfl

theorem graphEnergyBilinear_coercive (n : ℕ) (hn : 3 ≤ n) (r : ℝ) :
    IsCoercive (graphEnergyBilinear n r) := by
  let K := ‖graphEnergyInverse n r‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨(K^2)⁻¹, by positivity, ?_⟩
  intro x
  have hbound : ‖x‖ ≤ K * ‖graphEnergyMap n r x‖ := by
    calc
      ‖x‖ = ‖graphEnergyInverse n r (graphEnergyTransform n r x)‖ := by
        rw [graphEnergyInverse_left n hn r]
        rfl
      _ ≤ ‖graphEnergyInverse n r‖ * ‖graphEnergyMap n r x‖ :=
        (graphEnergyInverse n r).le_opNorm _
      _ ≤ K * ‖graphEnergyMap n r x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        dsimp [K]
        linarith
  rw [graphEnergyBilinear_apply, real_inner_self_eq_norm_sq]
  have hsquare : ‖x‖^2 ≤ K^2 * ‖graphEnergyMap n r x‖^2 := by
    nlinarith [norm_nonneg x, norm_nonneg (graphEnergyMap n r x)]
  calc
    (K^2)⁻¹ * ‖x‖ * ‖x‖ = ‖x‖^2 / K^2 := by ring
    _ ≤ ‖graphEnergyMap n r x‖^2 := (div_le_iff₀ (sq_pos_of_pos hK)).2 (by simpa only [mul_comm] using hsquare)

/-- For each continuous source functional on the original graph, the
original positive angular energy has a unique graph weak solution.
This theorem supplies existence, without assuming a solution. -/
theorem graph_weak_solution_exists_unique (n : ℕ) (hn : 3 ≤ n) (r : ℝ)
    (F : dirichletGraph →L[ℝ] ℝ) :
    ∃! x : dirichletGraph, ∀ y : dirichletGraph,
      graphEnergyBilinear n r x y = F y := by
  letI : CompleteSpace dirichletGraph := dirichletGraph_isClosed.completeSpace_coe
  let h := graphEnergyBilinear_coercive n hn r
  let f := (InnerProductSpace.toDual ℝ dirichletGraph).symm F
  let e := h.continuousLinearEquivOfBilin
  refine ⟨e.symm f, ?_, ?_⟩
  · intro y
    rw [← h.continuousLinearEquivOfBilin_apply]
    change inner ℝ (e (e.symm f)) y = F y
    rw [e.apply_symm_apply]
    exact InnerProductSpace.toDual_symm_apply
  · intro x hx
    apply e.injective
    have he : e x = f := by
      apply (InnerProductSpace.toDual ℝ dirichletGraph).injective
      ext y
      rw [InnerProductSpace.toDual_apply_apply, h.continuousLinearEquivOfBilin_apply, hx]
      simp [f]
    simpa using he

end
end DFL.GCI
