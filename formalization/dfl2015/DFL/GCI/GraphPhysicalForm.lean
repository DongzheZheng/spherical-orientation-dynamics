import DFL.GCI.GraphLaxMilgram

/-! The graph Lax--Milgram construction with the actual original angular
source and the exact original transformed energy density. -/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem graph_ae_interior : ∀ᵐ θ ∂angularLebesgue, θ ∈ Set.Ioo (0 : ℝ) Real.pi := by
  have h := ae_restrict_mem (s := Set.Ioc (0 : ℝ) Real.pi) measurableSet_Ioc (μ := (volume : Measure ℝ))
  have hp : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ Real.pi := (volume : Measure ℝ).ae_ne Real.pi
  filter_upwards [h, ae_restrict_of_ae hp] with θ hθ hpθ
  exact ⟨hθ.1, lt_of_le_of_ne hθ.2 hpθ⟩

def graphSourceDensity (n : ℕ) (r θ : ℝ) : ℝ :=
  Real.exp (r * Real.cos θ) * Real.rpow (Real.sin θ) (halfPower n + 2)

theorem graphSourceDensity_continuous (n : ℕ) (hn : 3 ≤ n) (r : ℝ) :
    Continuous (graphSourceDensity n r) := by
  have h : 0 ≤ halfPower n + 2 := by
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    unfold halfPower
    linarith
  exact (by fun_prop : Continuous (fun θ => Real.exp (r * Real.cos θ))).mul
    ((Real.continuous_rpow_const h).comp Real.continuous_sin)

theorem graphSourceDensity_memLp (n : ℕ) (hn : 3 ≤ n) (r : ℝ) :
    MemLp (graphSourceDensity n r) 2 angularLebesgue := by
  apply (memLp_two_iff_integrable_sq (graphSourceDensity_continuous n hn r).aestronglyMeasurable).2
  exact ((graphSourceDensity_continuous n hn r).pow 2).intervalIntegrable 0 Real.pi |>.1

def graphPhysicalSource (n : ℕ) (hn : 3 ≤ n) (r : ℝ) :
    dirichletGraph →L[ℝ] ℝ :=
  (innerSL ℝ ((graphSourceDensity_memLp n hn r).toLp (graphSourceDensity n r))).comp
    (graphSingular.comp dirichletGraph.subtypeL)

private theorem real_scalar_inner (x y : ℝ) : inner ℝ x y = x * y := by
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
  simp [mul_comm]

theorem graphPhysicalSource_integral (n : ℕ) (hn : 3 ≤ n) (r : ℝ)
    (p : dirichletGraph) :
    graphPhysicalSource n hn r p =
      ∫ θ, graphSourceDensity n r θ * (graphSingular p) θ ∂angularLebesgue := by
  change inner ℝ ((graphSourceDensity_memLp n hn r).toLp _) (graphSingular p) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(graphSourceDensity_memLp n hn r).coeFn_toLp] with θ hθ
  rw [hθ, real_scalar_inner]

theorem graphEnergyTransform_fst_ae (n : ℕ) (r : ℝ) (p : AngularGraphAmbient) :
    (graphDerivative (graphEnergyTransform n r p) : ℝ → ℝ) =ᵐ[angularLebesgue]
      fun θ => Real.exp (r * Real.cos θ / 2) *
        ((graphDerivative p) θ - halfPower n * Real.cos θ * (graphSingular p) θ) := by
  let d := graphDerivative p - halfPower n • cosineMultiplier (graphSingular p)
  have hw := graphWeight_ae r d
  have hs := Lp.coeFn_sub (graphDerivative p) (halfPower n • cosineMultiplier (graphSingular p))
  have ha := Lp.coeFn_smul (halfPower n) (cosineMultiplier (graphSingular p))
  have hc := l2MulCLM_ae Real.cos Real.continuous_cos.aestronglyMeasurable 1 (by norm_num)
    (ae_of_all _ (by intro θ; simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one θ))
    (graphSingular p)
  change (cosineMultiplier (graphSingular p) : ℝ → ℝ) =ᵐ[angularLebesgue]
    (fun θ => Real.cos θ * (graphSingular p) θ) at hc
  change (graphWeight r d : ℝ → ℝ) =ᵐ[angularLebesgue] _
  filter_upwards [hw, hs, ha, hc] with θ hwθ hsθ haθ hcθ
  rw [hwθ]
  rw [show d θ = (graphDerivative p) θ - (halfPower n • cosineMultiplier (graphSingular p)) θ by
    exact hsθ]
  rw [haθ]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hcθ]
  ring

theorem graphEnergyTransform_snd_ae (n : ℕ) (r : ℝ) (p : AngularGraphAmbient) :
    (graphSingular (graphEnergyTransform n r p) : ℝ → ℝ) =ᵐ[angularLebesgue]
      fun θ => Real.sqrt ((n : ℝ) - 2) * Real.exp (r * Real.cos θ / 2) *
        (graphSingular p) θ := by
  change (Real.sqrt ((n : ℝ) - 2) • graphWeight r (graphSingular p) : AngularL2) =ᵐ[angularLebesgue] _
  filter_upwards [Lp.coeFn_smul (Real.sqrt ((n : ℝ) - 2)) (graphWeight r (graphSingular p)),
    graphWeight_ae r (graphSingular p)] with θ hsmul hw
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hw]
  ring

def graphPhysicalFormDensity (n : ℕ) (r : ℝ) (p q : AngularGraphAmbient) (θ : ℝ) : ℝ :=
  Real.exp (r * Real.cos θ) *
    (((graphDerivative p) θ - halfPower n * Real.cos θ * (graphSingular p) θ) *
      ((graphDerivative q) θ - halfPower n * Real.cos θ * (graphSingular q) θ) +
      ((n : ℝ) - 2) * (graphSingular p) θ * (graphSingular q) θ)

theorem graphEnergyBilinear_integral (n : ℕ) (hn : 3 ≤ n) (r : ℝ)
    (p q : dirichletGraph) :
    graphEnergyBilinear n r p q =
      ∫ θ, graphPhysicalFormDensity n r p q θ ∂angularLebesgue := by
  have hb : 0 ≤ (n : ℝ) - 2 := by
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [graphEnergyBilinear_apply, WithLp.prod_inner_apply]
  rw [L2.inner_def, L2.inner_def, ← integral_add
    (L2.integrable_inner (𝕜 := ℝ) _ _) (L2.integrable_inner (𝕜 := ℝ) _ _)]
  apply integral_congr_ae
  filter_upwards [graphEnergyTransform_fst_ae n r p, graphEnergyTransform_fst_ae n r q,
    graphEnergyTransform_snd_ae n r p, graphEnergyTransform_snd_ae n r q]
    with θ hp1 hq1 hp2 hq2
  change inner ℝ ((graphDerivative (graphEnergyTransform n r p)) θ)
      ((graphDerivative (graphEnergyTransform n r q)) θ) +
    inner ℝ ((graphSingular (graphEnergyTransform n r p)) θ)
      ((graphSingular (graphEnergyTransform n r q)) θ) = _
  rw [hp1, hq1, hp2, hq2, real_scalar_inner, real_scalar_inner]
  unfold graphPhysicalFormDensity
  have hexp : Real.exp (r * Real.cos θ / 2) ^ 2 = Real.exp (r * Real.cos θ) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsqrt := Real.sq_sqrt hb
  conv_rhs => rw [← hexp, ← hsqrt]
  ring

theorem graphPhysicalFormDensity_integrable (n : ℕ) (hn : 3 ≤ n) (r : ℝ)
    (p q : AngularGraphAmbient) :
    Integrable (graphPhysicalFormDensity n r p q) angularLebesgue := by
  have hb : 0 ≤ (n : ℝ) - 2 := by
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hi := (L2.integrable_inner (𝕜 := ℝ)
    (graphDerivative (graphEnergyTransform n r p)) (graphDerivative (graphEnergyTransform n r q))).add
    (L2.integrable_inner (𝕜 := ℝ)
    (graphSingular (graphEnergyTransform n r p)) (graphSingular (graphEnergyTransform n r q)))
  apply hi.congr
  filter_upwards [graphEnergyTransform_fst_ae n r p, graphEnergyTransform_fst_ae n r q,
    graphEnergyTransform_snd_ae n r p, graphEnergyTransform_snd_ae n r q]
    with θ hp1 hq1 hp2 hq2
  simp only [Pi.add_apply]
  rw [hp1, hq1, hp2, hq2, real_scalar_inner, real_scalar_inner]
  unfold graphPhysicalFormDensity
  have hexp : Real.exp (r * Real.cos θ / 2) ^ 2 = Real.exp (r * Real.cos θ) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsqrt := Real.sq_sqrt hb
  conv_rhs => rw [← hexp, ← hsqrt]
  ring

/-- The actual forcing, not an assumed graph functional, has a unique
solution for every ambient dimension greater than two and every field. -/
theorem graph_original_source_exists_unique (n : ℕ) (hn : 3 ≤ n) (r : ℝ) :
    ∃! p : dirichletGraph, ∀ q : dirichletGraph,
      graphEnergyBilinear n r p q = graphPhysicalSource n hn r q :=
  graph_weak_solution_exists_unique n hn r (graphPhysicalSource n hn r)

end
end DFL.GCI
