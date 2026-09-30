import continuation.CompactPotentialGround
import continuation.ClassicalPotentialWeak

/-! The first positive full-domain eigenstate from the original constrained
minimum. Ground positivity and the genuine classical PDE discharge both
nonnegativity and simplicity of the zero eigenvalue. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Operator
open DFLSphere
namespace DFLCompactPotential
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable [VectorBundle ℝ E (TangentSpace I : M → Type _)]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance (g : SmoothRiemannianMetric I M) : IsFiniteMeasure (volume g) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
private local instance (g : SmoothRiemannianMetric I M) : (volume g).IsOpenPosMeasure :=
  riemannianVolumeMeasure_isOpenPosMeasure g

/-- The true first positive Schrödinger eigenstate and its full H1
Rayleigh minimum, derived from a positive normalized classical zero state.
The auxiliary ground is not assumed to minimize the Rayleigh quotient. -/
theorem positive_zero_ground_first_positive_exists (g : SmoothRiemannianMetric I M)
    (V : C^∞⟮I, M; ℝ⟯) (e : SmoothScalar g) (hen : ‖smoothToLp g e‖ = 1)
    (hep : ∀ x, 0 < e.toFun x)
    (heig : ∀ x, -ΔG g e.toContMDiffMap x+V x*e.toFun x = 0*e.toFun x)
    (horth : ∃ W : H1Compl g, H1ComplToLp g W ≠ 0 ∧
      ⟪H1ComplToLp g W,smoothToLp g e⟫_ℝ = 0) :
    ∃ (lam : ℝ) (u : SmoothScalar g), 0 < lam ∧ ‖smoothToLp g u‖ = 1 ∧
      ⟪smoothToLp g u,smoothToLp g e⟫_ℝ = 0 ∧
      (∀ x, -ΔG g u.toContMDiffMap x+V x*u.toFun x = lam*u.toFun x) ∧
      (∀ W : H1Compl g, ⟪H1ComplToLp g W,smoothToLp g e⟫_ℝ = 0 →
        lam*‖H1ComplToLp g W‖^2 ≤ potentialEnergy g V W) ∧
      IsWeakPotentialEigenstate g V lam (smoothToH1Compl g u) := by
  let J := H1ComplToLp g
  let eH := smoothToH1Compl g e
  have heH : J eH = smoothToLp g e := H1ComplToLp_smoothToH1Compl g e
  have hVtop : MemLp (V : M → ℝ) ∞ (volume g) :=
    V.contMDiff.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let P := boundedPotentialMultiplication (V : M → ℝ) hVtop
  have hP : P.IsSymmetric := boundedPotentialMultiplication_symmetric V hVtop
  have heweak := DFLClassicalPotentialWeak.smooth_classical_potential_eigen_weak
    g V hVtop 0 e heig
  have hsym (U W : H1Compl g) : potentialForm J P U W = potentialForm J P W U := by
    have hp : ⟪P (J U),J W⟫_ℝ = ⟪P (J W),J U⟫_ℝ :=
      (hP (J U) (J W)).trans (real_inner_comm _ _)
    simp only [potentialForm,hp,real_inner_comm U W,real_inner_comm (J U) (J W)]
  have hJ0 : ∃ U : H1Compl g, J U ≠ 0 := by
    refine ⟨eH,?_⟩
    rw [heH]
    exact norm_ne_zero_iff.mp (by rw [hen]; norm_num)
  obtain ⟨a,f,hfn,hfp,hfe,hmin,hfeig⟩ := positive_smooth_potential_ground_exists g V hJ0
  have hfweak := DFLClassicalPotentialWeak.smooth_classical_potential_eigen_weak
    g V hVtop a f hfeig
  have ha : a = 0 := by
    have hpair : 0 < ⟪smoothToLp g f,smoothToLp g e⟫_ℝ := by
      have hc : Continuous (fun x : M => f.toFun x*e.toFun x) :=
        f.smooth.continuous.mul e.smooth.continuous
      have hi : Integrable (fun x : M => f.toFun x*e.toFun x) (volume g) :=
        hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hp := integral_pos_of_integrable_nonneg_nonzero hc hi
        (fun x => (mul_pos (hfp x) (hep x)).le)
        (mul_pos (hfp (Classical.arbitrary M)) (hep (Classical.arbitrary M))).ne'
      have heq : ⟪smoothToLp g f,smoothToLp g e⟫_ℝ =
          ∫ x, f.toFun x*e.toFun x ∂volume g := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [f.memLp_two.coeFn_toLp,e.memLp_two.coeFn_toLp] with x hx hy
        have hxf : smoothToLp g f x = f.toFun x := hx
        have hye : smoothToLp g e x = e.toFun x := hy
        simp only [hxf,hye,RCLike.inner_apply,conj_trivial]
        ring
      rw [heq]
      exact hp
    have hw := hfweak eH
    have hz := heweak (smoothToH1Compl g f)
    change potentialForm J P eH (smoothToH1Compl g f) = 0*⟪J eH,J _⟫_ℝ at hz
    change potentialForm J P (smoothToH1Compl g f) eH = a*⟪J _,J eH⟫_ℝ at hw
    rw [hsym,hz,zero_mul] at hw
    rw [H1ComplToLp_smoothToH1Compl,heH] at hw
    exact (mul_eq_zero.mp hw.symm).resolve_right hpair.ne'
  have hn (W : H1Compl g) : 0 ≤ potentialForm J P W W := by
    have hh := hmin W
    rw [ha,zero_mul] at hh
    rw [actual_potential_form_diag]
    exact hh
  have hs (U : H1Compl g) (hU : ∀ W, potentialForm J P U W = 0) :
      ∃ c : ℝ, J U = c • J eH := by
    have huw : IsWeakPotentialEigenstate g V 0 U := by
      intro W
      have hh := hU W
      rw [actual_potential_form_eq] at hh
      simpa only [zero_mul] using hh
    obtain ⟨c,hc⟩ := positive_potential_weak_eigenspace_simple g V 0 e hep heig U huw
    refine ⟨c,?_⟩
    rw [hc,map_smul]
  obtain ⟨lam,U,hl,hu,hm,hw,hlo⟩ := compact_potential_first_positive_exists J
    (H1ComplToLp_isCompactOperator g) P hP eH (by rw [heH]; exact hen)
    (fun W => by simpa only [zero_mul] using heweak W) hn hs
    (by simpa only [heH] using horth)
  have huw : IsWeakPotentialEigenstate g V lam U := by
    intro W
    have hh := hw W
    rw [actual_potential_form_eq] at hh
    exact hh
  obtain ⟨u,hU,hueig⟩ := weak_smooth_potential_eigen_pointwise g V lam U huw
  refine ⟨lam,u,hl,?_,?_,hueig,?_,?_⟩
  · rw [hU,H1ComplToLp_smoothToH1Compl] at hu
    exact hu
  · rw [hU,H1ComplToLp_smoothToH1Compl,heH] at hm
    exact hm
  · intro W hW
    have hh := hlo W (by rw [heH]; exact hW)
    rw [actual_potential_form_diag] at hh
    exact hh
  · rw [hU] at huw
    exact huw

end DFLCompactPotential
