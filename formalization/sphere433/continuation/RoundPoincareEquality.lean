import continuation.GenericRoundPoincare
import continuation.PositiveGroundOrthogonal
import continuation.OrthogonalStationarity
import DFLSphere433.RoundSphereFirstEigenspace

/-! Equality in the genuine sharp sphere Poincare inequality implies
the actual first eigen-equation by constrained variational stationarity.
Elliptic regularity and the proved round first eigenspace identify all
equality states as ambient linear functions, including the circle. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold MeasureTheory Metric Module Set Filter
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.Integral.Measure
open DFLSphere DFLCompactPotential DFLDriftBaseline
namespace DFLGenericRound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

/-- Equality of the actual full H¹ energy yields an actual smooth first
eigenfunction representative; the eigen-equation is proved, not assumed. -/
theorem round_h1_poincare_equality_eigen (hn : 1≤n)
    (U : H1Compl (roundMetric (E := E) (n := n)))
    (hmean : (∫ x, H1ComplToLp (roundMetric (E := E) (n := n)) U x
      ∂roundVolume (E := E) (n := n))=0)
    (heq : ‖U‖^2-‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖^2=
      (n : ℝ)*‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖^2) :
    ∃s : SmoothScalar (roundMetric (E := E) (n := n)),
      U=smoothToH1Compl (roundMetric (E := E) (n := n)) s ∧
      ∀x,ΔG (roundMetric (E := E) (n := n)) s.toContMDiffMap x=-(n : ℝ)*s.toFun x := by
  let _ : NeZero n := ⟨by omega⟩
  let _ : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := ⟨by simp; omega⟩
  let _ : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E=n+1)
  obtain ⟨p,hp⟩ := (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ)≤1) :
    (sphere (0 : E) 1).Nonempty)
  have hpn : ‖p‖=1 := mem_sphere_zero_iff_norm.mp hp
  let g := roundMetric (E := E) (n := n)
  let J := H1ComplToLp g
  let V : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯ := ⟨fun _=>0,contMDiff_const⟩
  let _ : IsFiniteMeasure (roundVolume (E := E) (n := n)) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hV : MemLp (V : sphere (0 : E) 1 → ℝ) ∞ (roundVolume (E := E) (n := n)) :=
    V.contMDiff.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let P := boundedPotentialMultiplication (V : sphere (0 : E) 1 → ℝ) hV
  obtain ⟨e,hen,_hep,heig,hexp,_W,_hW,_ho⟩ := actual_drift_normalized_zero_orthogonal_exists (n := n) p hpn 0
  obtain ⟨c,hc,hce⟩ := hexp
  have hec (x : sphere (0 : E) 1) : e.toFun x=c := by
    rw [hce]
    change c*Real.exp ((0/2)*⟪p,(x : E)⟫_ℝ)=c
    simp
  have heq0 (x : sphere (0 : E) 1) : -ΔG g e.toContMDiffMap x+V x*e.toFun x=0*e.toFun x := by
    have hh := heig x
    simp only [driftPotential,zero_pow (by decide : 2≠0),zero_div,zero_mul,sub_zero,add_zero] at hh
    change -ΔG g e.toContMDiffMap x+0*e.toFun x=0*e.toFun x
    simpa only [zero_mul,add_zero] using hh
  have hpair (W : H1Compl g) : ⟪J W,smoothToLp g e⟫_ℝ=
      c*(∫x,J W x ∂roundVolume (E := E) (n := n)) := by
    rw [L2.inner_def]
    calc
      _=∫x,c*J W x ∂roundVolume (E := E) (n := n) := by
        apply integral_congr_ae
        filter_upwards [e.memLp_two.coeFn_toLp] with x hx
        have hx' : smoothToLp g e x=e.toFun x := hx
        rw [hx',hec x,Real.inner_apply]
        ring
      _=_ := integral_const_mul _ _
  have hdiag (W : H1Compl g) : potentialForm J P W W=‖W‖^2-‖J W‖^2 := by
    rw [actual_potential_form_diag]
    change ‖W‖^2-‖J W‖^2+(∫x,(0 : ℝ)*(J W x)^2 ∂roundVolume (E := E) (n := n))=_
    simp only [zero_mul,integral_zero,add_zero]
  have heweak := DFLClassicalPotentialWeak.smooth_classical_potential_eigen_weak g V hV 0 e heq0
  have hmin (W : H1Compl g) (hW : ⟪J W,J (smoothToH1Compl g e)⟫_ℝ=0) :
      (n : ℝ)*‖J W‖^2≤potentialForm J P W W := by
    rw [H1ComplToLp_smoothToH1Compl] at hW
    rw [hpair] at hW
    have hm := (mul_eq_zero.mp hW).resolve_left hc.ne'
    rw [hdiag]
    exact round_sphere_h1_poincare hn W hm
  have hweak := orthogonal_potential_minimizer_weak J P
    (boundedPotentialMultiplication_symmetric V hV) (smoothToH1Compl g e) U
    (by rw [H1ComplToLp_smoothToH1Compl]; exact hen)
    (fun W => by simpa only [zero_mul] using heweak W)
    (by rw [H1ComplToLp_smoothToH1Compl,hpair,hmean,mul_zero])
    (n : ℝ) (by rw [hdiag]; exact heq) hmin
  have hU : IsWeakPotentialEigenstate g V (n : ℝ) U := by
    intro W
    have hh := hweak W
    rw [actual_potential_form_eq] at hh
    exact hh
  obtain ⟨s,hUs,hs⟩ := weak_smooth_potential_eigen_pointwise g V (n : ℝ) U hU
  refine ⟨s,hUs,?_⟩
  intro x
  have hh := hs x
  change -ΔG g s.toContMDiffMap x+0*s.toFun x=(n : ℝ)*s.toFun x at hh
  linarith

/-- Complete full H¹ equality classification in the actual round metric. -/
theorem round_h1_poincare_equality_exists_linear (hn : 1≤n)
    (U : H1Compl (roundMetric (E := E) (n := n)))
    (hmean : (∫ x, H1ComplToLp (roundMetric (E := E) (n := n)) U x
      ∂roundVolume (E := E) (n := n))=0)
    (heq : ‖U‖^2-‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖^2=
      (n : ℝ)*‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖^2) :
    ∃a : E,(H1ComplToLp (roundMetric (E := E) (n := n)) U : sphere (0 : E) 1 → ℝ)
      =ᵐ[roundVolume (E := E) (n := n)] (fun x=>⟪a,(x : E)⟫_ℝ) := by
  let _ : NeZero n := ⟨by omega⟩
  obtain ⟨s,hU,hs⟩ := round_h1_poincare_equality_eigen hn U hmean heq
  obtain ⟨a,ha⟩ := DFLFirstEigenspace.round_first_eigenfunction_exists_linear s.toContMDiffMap hs
  refine ⟨a,?_⟩
  rw [hU,H1ComplToLp_smoothToH1Compl]
  exact s.memLp_two.coeFn_toLp.trans (ae_of_all _ ha)

/-- Actual angular equality implies a linear slice, with no eigen-equation
or eigenspace identification supplied as a premise. -/
theorem round_smooth_poincare_equality_exists_linear (hn : 1≤n)
    (f : C^∞⟮𝓡 n,sphere (0 : E) 1;ℝ⟯)
    (hmean : (∫x,f x ∂roundVolume (E := E) (n := n))=0)
    (heq : (∫x,normGradSqFun (roundMetric (E := E) (n := n)) f x
      ∂roundVolume (E := E) (n := n))=(n : ℝ)*
      (∫x,(f x)^2 ∂roundVolume (E := E) (n := n))) :
    ∃a : E,∀x : sphere (0 : E) 1,f x=⟪a,(x : E)⟫_ℝ := by
  let g := roundMetric (E := E) (n := n)
  let s : SmoothScalar g := ⟨f,f.contMDiff⟩
  have hM : (∫x,H1ComplToLp g (smoothToH1Compl g s) x ∂roundVolume (E := E) (n := n))=0 := by
    rw [H1ComplToLp_smoothToH1Compl]
    exact (integral_congr_ae s.memLp_two.coeFn_toLp).trans hmean
  have hN : ‖H1ComplToLp g (smoothToH1Compl g s)‖^2=
      ∫x,(f x)^2 ∂roundVolume (E := E) (n := n) := by
    rw [H1ComplToLp_smoothToH1Compl]
    calc
      _=∫x,f x*f x ∂roundVolume (E := E) (n := n) := s.norm_smoothToLp_sq
      _=_ := by apply integral_congr_ae; filter_upwards [] with x; ring
  obtain ⟨a,ha⟩ := round_h1_poincare_equality_exists_linear hn (smoothToH1Compl g s) hM
    (by rw [DFLSphere.h1_smooth_energy,hN]; exact heq)
  let _ : (roundVolume (E := E) (n := n)).IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  have hfAE : (f : sphere (0 : E) 1 → ℝ)=ᵐ[roundVolume (E := E) (n := n)] fun x=>⟪a,(x : E)⟫_ℝ := by
    rw [H1ComplToLp_smoothToH1Compl] at ha
    exact s.memLp_two.coeFn_toLp.symm.trans ha
  refine ⟨a,?_⟩
  exact congrFun (MeasureTheory.Measure.eq_of_ae_eq hfAE f.contMDiff.continuous
    (continuous_const.inner continuous_subtype_val))

end DFLGenericRound
