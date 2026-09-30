import DFL.GCI.ZeroMeanSmoothDensity
import Mathlib.Analysis.Calculus.Deriv.Support

/-! The classical Dirichlet `H¹₀` completion on `(0,π)`.
It is defined here by its conventional smooth-test function/derivative
`L² × L²` graph closure, and identified with the integral-primitive graph.
This does not rename the additional singular-integrability condition in
`AngularEnergyDomain`. -/

namespace DFL.GCI
open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
noncomputable section

/-- A zero-mean interior test has an interior compactly supported primitive. -/
theorem compactTestPrimitive_interior_support (ψ : ℝ → ℝ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ioo 0 Real.pi)
    (hzero : (∫ x, ψ x) = 0) :
    tsupport (compactTestPrimitive ψ) ⊆ Ioo 0 Real.pi := by
  by_cases hne : (tsupport ψ).Nonempty
  · obtain ⟨a, ha⟩ := hc.isCompact.exists_isLeast hne
    obtain ⟨b, hb⟩ := hc.isCompact.exists_isGreatest hne
    have hsupport : Function.support (compactTestPrimitive ψ) ⊆ Icc a b := by
      intro x hx
      have hxne : compactTestPrimitive ψ x ≠ 0 := hx
      constructor
      · by_contra hax
        have hxa : x < a := lt_of_not_ge hax
        apply hxne
        unfold compactTestPrimitive
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Iic] with t ht
        by_contra htne
        have hat := ha.2 (subset_tsupport ψ htne)
        exact (not_lt_of_ge (hat.trans ht)).elim hxa
      · by_contra hxb
        have hbx : b < x := lt_of_not_ge hxb
        apply hxne
        unfold compactTestPrimitive
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero (by
          intro t ht
          by_contra htne
          have htb := hb.2 (subset_tsupport ψ htne)
          have hxt : x < t := lt_of_not_ge ht
          exact (not_lt_of_ge htb).elim (hbx.trans hxt)), hzero]
    apply (closure_minimal hsupport isClosed_Icc).trans
    intro x hx
    exact ⟨(hs ha.1).1.trans_le hx.1, hx.2.trans_lt (hs hb.1).2⟩
  · have hψ : ψ = 0 := by
      funext x
      by_contra hx
      exact hne ⟨x, subset_tsupport ψ hx⟩
    have hP : compactTestPrimitive ψ = 0 := by
      funext x
      simp [compactTestPrimitive, hψ]
    simp [hP]

theorem compactTestPrimitive_eq_interval_of_interior (ψ : ℝ → ℝ)
    (hd : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ioo 0 Real.pi) (x : ℝ) :
    compactTestPrimitive ψ x = ∫ t in (0 : ℝ)..x, ψ t := by
  have hi : Integrable ψ volume := hd.integrable_of_hasCompactSupport hc
  have hleft : (∫ t in Iic (0 : ℝ), ψ t) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Iic] with t ht
    by_contra hne
    exact (not_lt_of_ge ht).elim (hs (subset_tsupport ψ hne)).1
  have h := intervalIntegral.integral_Iic_sub_Iic
    (a := (0 : ℝ)) (b := x) hi.integrableOn hi.integrableOn
  unfold compactTestPrimitive
  linarith

theorem l2Primitive_congr_test (q : AngularL2) (ψ : ℝ → ℝ)
    (hψ : (q : ℝ → ℝ) =ᵐ[angularLebesgue] ψ) {x : ℝ}
    (hx : x ∈ Icc 0 Real.pi) : l2Primitive q x = ∫ t in (0 : ℝ)..x, ψ t := by
  calc
    l2Primitive q x = ∫ t in Ioc (0 : ℝ) x, ψ t ∂angularLebesgue :=
      integral_congr_ae (ae_restrict_of_ae hψ)
    _ = ∫ t in Ioc (0 : ℝ) x, ψ t := by
      unfold angularLebesgue
      rw [Measure.restrict_restrict_of_subset
        (by intro t ht; exact ⟨ht.1, ht.2.trans hx.2⟩)]
    _ = ∫ t in (0 : ℝ)..x, ψ t := (intervalIntegral.integral_of_le hx.1).symm

theorem interiorTest_zero_endpoint (φ : ℝ → ℝ) (hs : tsupport φ ⊆ Ioo 0 Real.pi) :
    φ 0 = 0 ∧ φ Real.pi = 0 := by
  constructor <;> by_contra hne
  · exact (lt_irrefl (0 : ℝ)) (hs (subset_tsupport φ hne)).1
  · exact (lt_irrefl Real.pi) (hs (subset_tsupport φ hne)).2

/-- The true smooth compact test graph, without a substitute weak derivative. -/
def smoothDirichletTestGraph : Set (AngularL2 × AngularL2) :=
  {p | ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
    tsupport φ ⊆ Ioo 0 Real.pi ∧
    (p.1 : ℝ → ℝ) =ᵐ[angularLebesgue] φ ∧
    (p.2 : ℝ → ℝ) =ᵐ[angularLebesgue] deriv φ}

/-- The conventional `H¹₀` completion: closure of smooth compact test
functions and their classical derivatives in `L² × L²`. -/
def classicalH10Graph : Set (AngularL2 × AngularL2) := closure smoothDirichletTestGraph

def h10PrimitiveConstraint : (AngularL2 × AngularL2) →L[ℝ] AngularL2 :=
  ContinuousLinearMap.fst ℝ AngularL2 AngularL2 -
    l2PrimitiveCLM.comp (ContinuousLinearMap.snd ℝ AngularL2 AngularL2)

def h10TraceConstraint : (AngularL2 × AngularL2) →L[ℝ] ℝ :=
  l2Mean.comp (ContinuousLinearMap.snd ℝ AngularL2 AngularL2)

def h10PrimitiveGraph : Submodule ℝ (AngularL2 × AngularL2) :=
  h10PrimitiveConstraint.ker ⊓ h10TraceConstraint.ker

theorem mem_h10PrimitiveGraph (p : AngularL2 × AngularL2) :
    p ∈ h10PrimitiveGraph ↔ p.1 = l2PrimitiveCLM p.2 ∧ l2Mean p.2 = 0 := by
  change (p.1 - l2PrimitiveCLM p.2 = 0 ∧ l2Mean p.2 = 0) ↔ _
  rw [sub_eq_zero]

theorem h10PrimitiveGraph_isClosed : IsClosed (h10PrimitiveGraph : Set (AngularL2 × AngularL2)) :=
  h10PrimitiveConstraint.isClosed_ker.inter h10TraceConstraint.isClosed_ker

theorem smoothDirichletTestGraph_subset_primitive :
    smoothDirichletTestGraph ⊆ (h10PrimitiveGraph : Set (AngularL2 × AngularL2)) := by
  rintro p ⟨φ, hd, _, hs, hu, hq⟩
  have hφ0 := (interiorTest_zero_endpoint φ hs).1
  have hφπ := (interiorTest_zero_endpoint φ hs).2
  have hdc : Continuous (deriv φ) := hd.continuous_deriv (by simp)
  have hdiff : Differentiable ℝ φ := hd.differentiable (by simp)
  have hprim (x : ℝ) (hx : x ∈ Icc 0 Real.pi) : l2Primitive p.2 x = φ x := by
    rw [l2Primitive_congr_test p.2 (deriv φ) hq hx,
      intervalIntegral.integral_deriv_eq_sub (fun t _ => hdiff t) (hdc.intervalIntegrable 0 x),
      hφ0, sub_zero]
  apply (mem_h10PrimitiveGraph p).mpr
  constructor
  · apply Lp.ext
    filter_upwards [hu, l2PrimitiveCLM_ae p.2, angularLebesgue_ae_interior] with x hux hpx hx
    rw [hux, hpx, hprim x ⟨hx.1.le, hx.2.le⟩]
  · rw [l2Mean_eq_integral, integral_congr_ae hq]
    change (∫ t in Ioc (0 : ℝ) Real.pi, deriv φ t) = 0
    rw [← intervalIntegral.integral_of_le Real.pi_pos.le,
      intervalIntegral.integral_deriv_eq_sub (fun t _ => hdiff t)
        (hdc.intervalIntegrable 0 Real.pi), hφ0, hφπ, sub_self]

def zeroMeanSmoothTests : Set AngularL2 :=
  {q | ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
    tsupport ψ ⊆ Ioo 0 Real.pi ∧ (∫ x, ψ x) = 0 ∧
    (q : ℝ → ℝ) =ᵐ[angularLebesgue] ψ}

theorem zeroMean_mem_closure_smooth (q : AngularL2) (hq : l2Mean q = 0) :
    q ∈ closure zeroMeanSmoothTests := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨ψ, hm, hd, hc, hs, hz, he⟩ := exists_zeroMean_smooth_approx q hq hε
  refine ⟨hm.toLp ψ, ⟨ψ, hd, hc, hs, hz, hm.coeFn_toLp⟩, ?_⟩
  simpa only [dist_eq_norm] using he

def h10GraphMap : AngularL2 →L[ℝ] (AngularL2 × AngularL2) :=
  l2PrimitiveCLM.prod (ContinuousLinearMap.id ℝ AngularL2)

theorem zeroMeanSmoothTests_graph_mem (q : AngularL2) (hq : q ∈ zeroMeanSmoothTests) :
    h10GraphMap q ∈ smoothDirichletTestGraph := by
  rcases hq with ⟨ψ, hd, hc, hs, hz, hq⟩
  let φ := compactTestPrimitive ψ
  have hderiv : deriv φ = ψ := by
    funext x
    exact (compactTestPrimitive_hasDerivAt ψ hd.continuous hc x).deriv
  refine ⟨φ, compactTestPrimitive_contDiff ψ hd hc,
    compactTestPrimitive_hasCompactSupport ψ hc hz,
    compactTestPrimitive_interior_support ψ hc hs hz, ?_, ?_⟩
  · change (l2PrimitiveCLM q : ℝ → ℝ) =ᵐ[angularLebesgue] φ
    filter_upwards [l2PrimitiveCLM_ae q, angularLebesgue_ae_interior] with x hpx hx
    rw [hpx, l2Primitive_congr_test q ψ hq ⟨hx.1.le, hx.2.le⟩]
    exact (compactTestPrimitive_eq_interval_of_interior ψ hd.continuous hc hs x).symm
  · change (q : ℝ → ℝ) =ᵐ[angularLebesgue] deriv φ
    rwa [hderiv]

/-- The standard smooth `H¹₀` completion equals the exact zero-trace
integral-primitive graph. Both directions are proved without density assumptions. -/
theorem classicalH10Graph_eq_primitiveGraph :
    classicalH10Graph = (h10PrimitiveGraph : Set (AngularL2 × AngularL2)) := by
  apply subset_antisymm
  · exact closure_minimal smoothDirichletTestGraph_subset_primitive h10PrimitiveGraph_isClosed
  · intro p hp
    rcases (mem_h10PrimitiveGraph p).mp hp with ⟨hu, hq⟩
    have hclos := mem_closure_image h10GraphMap.continuous.continuousAt
      (zeroMean_mem_closure_smooth p.2 hq)
    have himage : h10GraphMap '' zeroMeanSmoothTests ⊆ smoothDirichletTestGraph := by
      rintro _ ⟨q, hq, rfl⟩
      exact zeroMeanSmoothTests_graph_mem q hq
    have hpmap : h10GraphMap p.2 = p := Prod.ext hu.symm rfl
    rw [hpmap] at hclos
    exact closure_mono himage hclos

/-- A pair belongs to the conventional `H¹₀` completion precisely when its
value is the primitive of its derivative and the integral of that derivative vanishes. -/
theorem mem_classicalH10Graph_iff (u q : AngularL2) :
    (u, q) ∈ classicalH10Graph ↔ u = l2PrimitiveCLM q ∧ l2Mean q = 0 := by
  rw [classicalH10Graph_eq_primitiveGraph]
  exact mem_h10PrimitiveGraph (u, q)

end
end DFL.GCI
