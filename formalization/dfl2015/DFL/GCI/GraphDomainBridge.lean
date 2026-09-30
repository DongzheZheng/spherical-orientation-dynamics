import DFL.GCI.DirichletGraph
import DFL.GCI.EnergyDomainIntegrability

/-! Exact transport between the singular Hilbert graph and the original
Dirichlet representative domain. The original angular function is rebuilt
from the graph derivative's actual primitive, including both zero traces. -/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def graphState (n : ℕ) (p : dirichletGraph) : AngularState :=
  ⟨fun θ => l2Primitive (graphDerivative p) θ /
      Real.rpow (Real.sin θ) (halfPower n),
    graphDerivative p⟩

theorem graphState_scaled_reconstruction
    (n : ℕ) (hn : 3 ≤ n) (p : dirichletGraph) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    scaledFunction n (graphState n p) θ = l2Primitive (graphDerivative p) θ := by
  have ha : 0 < halfPower n := by
    unfold halfPower
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  by_cases h0 : θ = 0
  · subst θ
    simp [scaledFunction, graphState, l2Primitive, Real.zero_rpow ha.ne']
  by_cases hpi : θ = Real.pi
  · subst θ
    simp [scaledFunction, graphState, Real.zero_rpow ha.ne', dirichletGraph_zero_trace]
  have hθi : θ ∈ Set.Ioo (0 : ℝ) Real.pi :=
    ⟨lt_of_le_of_ne hθ.1 (Ne.symm h0), lt_of_le_of_ne hθ.2 hpi⟩
  have hpne := (Real.rpow_pos_of_pos (Real.sin_pos_of_mem_Ioo hθi) (halfPower n)).ne'
  change Real.rpow (Real.sin θ) (halfPower n) *
      (l2Primitive (graphDerivative p) θ / Real.rpow (Real.sin θ) (halfPower n)) = _
  field_simp [hpne]

theorem graphState_mem_energy
    (n : ℕ) (hn : 3 ≤ n) (p : dirichletGraph) :
    AngularEnergyDomain n (graphState n p) := by
  have hq : MemLp (graphDerivative p) 2 angularLebesgue := Lp.memLp _
  have hqint : IntervalIntegrable (graphDerivative p) volume (0 : ℝ) Real.pi := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mpr
    exact hq.integrable (by norm_num)
  have hq2 : IntervalIntegrable (fun θ => (graphDerivative p θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mpr
    exact hq.integrable_sq
  refine ⟨hqint, hq2, ?_, ?_, ?_⟩
  · intro θ hθ
    rw [graphState_scaled_reconstruction n hn p θ hθ]
    exact l2Primitive_eq_interval _ hθ
  · change (∫ θ in (0 : ℝ)..Real.pi, graphDerivative p θ) = 0
    rw [← l2Primitive_eq_interval _ ⟨Real.pi_pos.le, le_rfl⟩]
    exact dirichletGraph_zero_trace p
  · have hy : MemLp (graphSingular p) 2 angularLebesgue := Lp.memLp _
    have hyint : IntervalIntegrable
        (fun θ => ((n : ℝ) - 2) ^ 2 * (graphSingular p θ) ^ 2)
        volume (0 : ℝ) Real.pi := by
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mpr
      exact hy.integrable_sq.const_mul _
    apply hyint.congr_ae
    have hp := dirichletGraph_primitive_ae p
    have hp' : (fun θ => Real.sin θ * (graphSingular p) θ) =ᵐ[angularIntervalMeasure]
        l2Primitive (graphDerivative p) := by
      simpa only [angularIntervalMeasure, angularLebesgue, Set.uIoc_of_le Real.pi_pos.le] using hp
    filter_upwards [moment_ae_interior, hp'] with θ hθ hprim
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
    have hpow : Real.rpow (Real.sin θ) (halfPower n) =
        Real.rpow (Real.sin θ) (((n : ℝ) - 4) / 2) * Real.sin θ := by
      have he : ((n : ℝ) - 4) / 2 + 1 = halfPower n := by unfold halfPower; ring
      rw [← he]
      exact Real.rpow_add_one hsin.ne' _
    dsimp [graphState]
    have hpow' : (Real.sin θ) ^ (halfPower n) =
        (Real.sin θ) ^ (((n : ℝ) - 4) / 2) * Real.sin θ := hpow
    rw [← hprim, hpow']
    have hbp := (Real.rpow_pos_of_pos hsin (((n : ℝ) - 4) / 2)).ne'
    field_simp [hsin.ne', hbp]

theorem graphState_primitive (n : ℕ) (p : dirichletGraph) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    momentPrimitive (graphState n p) θ = l2Primitive (graphDerivative p) θ :=
  (l2Primitive_eq_interval _ hθ).symm

theorem graphState_singular_ae (n : ℕ) (p : dirichletGraph) :
    singularRepresentative (graphState n p) =ᵐ[angularLebesgue] graphSingular p := by
  have hθae : ∀ᵐ θ ∂angularLebesgue, θ ∈ Set.Ioo (0 : ℝ) Real.pi := by
    simpa only [angularLebesgue, angularIntervalMeasure, Set.uIoc_of_le Real.pi_pos.le] using
      moment_ae_interior
  filter_upwards [dirichletGraph_primitive_ae p, hθae] with θ hprim hθ
  unfold singularRepresentative
  rw [graphState_primitive n p θ ⟨hθ.1.le, hθ.2.le⟩, ← hprim]
  have hsin := (Real.sin_pos_of_mem_Ioo hθ).ne'
  field_simp [hsin]

theorem stateDerivative_memLp (n : ℕ) (s : AngularState)
    (hs : AngularEnergyDomain n s) :
    MemLp s.scaledDerivative 2 angularLebesgue := by
  simpa only [angularLebesgue, angularIntervalMeasure,
    Set.uIoc_of_le Real.pi_pos.le] using scaledDerivative_memLp_two n s hs

theorem stateSingular_memLp (n : ℕ) (hn : 3 ≤ n) (s : AngularState)
    (hs : AngularEnergyDomain n s) :
    MemLp (singularRepresentative s) 2 angularLebesgue := by
  simpa only [angularLebesgue, angularIntervalMeasure,
    Set.uIoc_of_le Real.pi_pos.le] using singularRepresentative_memLp_two n hn s hs

def stateDerivativeL2 (n : ℕ) (s : AngularState)
    (hs : AngularEnergyDomain n s) : AngularL2 :=
  (stateDerivative_memLp n s hs).toLp s.scaledDerivative

def stateSingularL2 (n : ℕ) (hn : 3 ≤ n) (s : AngularState)
    (hs : AngularEnergyDomain n s) : AngularL2 :=
  (stateSingular_memLp n hn s hs).toLp (singularRepresentative s)

theorem stateDerivativeL2_ae (n : ℕ) (s : AngularState)
    (hs : AngularEnergyDomain n s) :
    (stateDerivativeL2 n s hs : ℝ → ℝ) =ᵐ[angularLebesgue] s.scaledDerivative :=
  (stateDerivative_memLp n s hs).coeFn_toLp

theorem stateSingularL2_ae (n : ℕ) (hn : 3 ≤ n) (s : AngularState)
    (hs : AngularEnergyDomain n s) :
    (stateSingularL2 n hn s hs : ℝ → ℝ) =ᵐ[angularLebesgue] singularRepresentative s :=
  (stateSingular_memLp n hn s hs).coeFn_toLp

theorem stateDerivativeL2_primitive (n : ℕ) (s : AngularState)
    (hs : AngularEnergyDomain n s) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    l2Primitive (stateDerivativeL2 n s hs) θ = momentPrimitive s θ := by
  calc
    _ = ∫ x in Set.Ioc 0 θ, s.scaledDerivative x ∂angularLebesgue := by
      exact integral_congr_ae (ae_restrict_of_ae (stateDerivativeL2_ae n s hs))
    _ = _ := by
      unfold angularLebesgue momentPrimitive
      rw [Measure.restrict_restrict_of_subset
        (by intro x hx; exact ⟨hx.1, hx.2.trans hθ.2⟩)]
      exact (intervalIntegral.integral_of_le hθ.1).symm

def stateGraphAmbient (n : ℕ) (hn : 3 ≤ n) (s : AngularState)
    (hs : AngularEnergyDomain n s) : AngularGraphAmbient :=
  WithLp.toLp 2 (stateDerivativeL2 n s hs, stateSingularL2 n hn s hs)

theorem stateGraphAmbient_mem (n : ℕ) (hn : 3 ≤ n) (s : AngularState)
    (hs : AngularEnergyDomain n s) : stateGraphAmbient n hn s hs ∈ dirichletGraph := by
  refine ⟨?_, ?_⟩
  · change graphConstraint (stateGraphAmbient n hn s hs) = 0
    apply sub_eq_zero.mpr
    apply Lp.ext
    have hθae : ∀ᵐ θ ∂angularLebesgue, θ ∈ Set.Ioo (0 : ℝ) Real.pi := by
      simpa only [angularLebesgue, angularIntervalMeasure,
        Set.uIoc_of_le Real.pi_pos.le] using moment_ae_interior
    have hbound : ∀ᵐ θ ∂angularLebesgue, ‖Real.sin θ‖ ≤ (1 : ℝ) :=
      ae_of_all _ (by intro θ; simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one θ)
    filter_upwards [l2MulCLM_ae Real.sin Real.continuous_sin.aestronglyMeasurable 1
      (by norm_num) hbound (stateSingularL2 n hn s hs),
      l2PrimitiveCLM_ae (stateDerivativeL2 n s hs), stateSingularL2_ae n hn s hs,
      hθae] with θ hleft hright hy hθ
    change (sineMultiplier (stateSingularL2 n hn s hs)) θ =
      (l2PrimitiveCLM (stateDerivativeL2 n s hs)) θ
    change (sineMultiplier (stateSingularL2 n hn s hs)) θ =
      Real.sin θ * (stateSingularL2 n hn s hs) θ at hleft
    rw [hleft, hright, hy, stateDerivativeL2_primitive n s hs θ ⟨hθ.1.le, hθ.2.le⟩]
    unfold singularRepresentative
    field_simp [(Real.sin_pos_of_mem_Ioo hθ).ne']
  · change inner ℝ ((Lp.const 2 angularLebesgue) (1 : ℝ)) (stateDerivativeL2 n s hs) = 0
    rw [L2.inner_def]
    calc
      _ = ∫ θ, s.scaledDerivative θ ∂angularLebesgue := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_const 2 angularLebesgue (1 : ℝ),
          stateDerivativeL2_ae n s hs] with θ hc hq
        rw [hc, hq]
        simp only [Function.const_apply]
        rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
        simp
      _ = 0 := by
        simpa only [angularLebesgue, ← intervalIntegral.integral_of_le Real.pi_pos.le] using
          hs.2.2.2.1

def stateToGraph (n : ℕ) (hn : 3 ≤ n) (s : AngularState)
    (hs : AngularEnergyDomain n s) : dirichletGraph :=
  ⟨stateGraphAmbient n hn s hs, stateGraphAmbient_mem n hn s hs⟩

theorem stateToGraph_derivative_ae (n : ℕ) (hn : 3 ≤ n) (s : AngularState)
    (hs : AngularEnergyDomain n s) :
    (graphDerivative (stateToGraph n hn s hs) : ℝ → ℝ) =ᵐ[angularLebesgue]
      s.scaledDerivative := stateDerivativeL2_ae n s hs

theorem stateToGraph_singular_ae (n : ℕ) (hn : 3 ≤ n) (s : AngularState)
    (hs : AngularEnergyDomain n s) :
    (graphSingular (stateToGraph n hn s hs) : ℝ → ℝ) =ᵐ[angularLebesgue]
      singularRepresentative s := stateSingularL2_ae n hn s hs

theorem graphState_stateToGraph_g (n : ℕ) (hn : 3 ≤ n) (s : AngularState)
    (hs : AngularEnergyDomain n s) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    (graphState n (stateToGraph n hn s hs)).g θ = s.g θ := by
  change l2Primitive (stateDerivativeL2 n s hs) θ /
      Real.rpow (Real.sin θ) (halfPower n) = s.g θ
  rw [stateDerivativeL2_primitive n s hs θ ⟨hθ.1.le, hθ.2.le⟩,
    ← moment_reconstruction n s hs θ ⟨hθ.1.le, hθ.2.le⟩]
  field_simp [(Real.rpow_pos_of_pos (Real.sin_pos_of_mem_Ioo hθ) (halfPower n)).ne']

end
end DFL.GCI
