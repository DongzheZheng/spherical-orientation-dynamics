import continuation.CotAngularProjection
import continuation.EvenSquareFiniteProfile
import continuation.LatMeasureIdentity
import DifferentialGeometry.Geometry.Metric.Sphere.Isometry.OrthogonalAction
import DifferentialGeometry.Analysis.Integration.Measure.Pullback

/-! The actual angular average has smooth even pole-radius representatives.
Joint smoothness of the genuine normalized sphere map and actual antipodal
volume invariance supply the pole regularity used by the original proof. -/
noncomputable section
set_option maxHeartbeats 1000000
open Bundle Manifold Metric Module Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DFLCotSphere DFLAngularMean
namespace DFLMeanSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E=n+2)]
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p) := borel (PolarDir p)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p) := ⟨rfl⟩
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

def poleAmbient (p : sphere (0 : E) 1) (eps : ℝ) (q : PolarDir p × ℝ) : E :=
  cotAngularScale q.2 • (eps • (p : E)+q.2 • ((q.1 : (ℝ ∙ (p : E))ᗮ) : E))

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E=n+2)] in
theorem poleAmbient_norm (p : sphere (0 : E) 1) (eps : ℝ) (heps : eps^2=1)
    (q : PolarDir p × ℝ) : ‖poleAmbient p eps q‖=1 := by
  have hpp : ⟪(p : E),(p : E)⟫_ℝ=1 := by
    rw [real_inner_self_eq_norm_sq,norm_eq_of_mem_sphere p]; norm_num
  have hyy : ⟪((q.1 : (ℝ ∙ (p : E))ᗮ) : E),((q.1 : (ℝ ∙ (p : E))ᗮ) : E)⟫_ℝ=1 := by
    rw [real_inner_self_eq_norm_sq]
    change ‖(q.1 : (ℝ ∙ (p : E))ᗮ)‖^2=1
    rw [norm_eq_of_mem_sphere q.1]; norm_num
  have hpy : ⟪(p : E),((q.1 : (ℝ ∙ (p : E))ᗮ) : E)⟫_ℝ=0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (q.1 : (ℝ ∙ (p : E))ᗮ).property
  have hyp : ⟪((q.1 : (ℝ ∙ (p : E))ᗮ) : E),(p : E)⟫_ℝ=0 := by
    rw [real_inner_comm]
    exact hpy
  have hscale : cotAngularScale q.2^2*(1+q.2^2)=1 := by
    rw [← cotLineScale_eq_square]
    exact inv_mul_cancel₀ (by positivity : (1+q.2^2) ≠ 0)
  have hs : ‖poleAmbient p eps q‖^2=1 := by
    rw [← real_inner_self_eq_norm_sq]
    unfold poleAmbient
    simp only [real_inner_smul_left,real_inner_smul_right,inner_add_left,inner_add_right,
      hpp,hyy,hpy,hyp,mul_zero,add_zero,zero_add,mul_one]
    nlinarith [congrArg (fun z : ℝ => cotAngularScale q.2^2*z) heps,hscale]
  nlinarith [norm_nonneg (poleAmbient p eps q)]

def poleFamily (p : sphere (0 : E) 1) (eps : ℝ) (heps : eps^2=1)
    (q : PolarDir p × ℝ) : sphere (0 : E) 1 :=
  ⟨poleAmbient p eps q,by rw [mem_sphere_zero_iff_norm]; exact poleAmbient_norm p eps heps q⟩

omit [FiniteDimensional ℝ E] in
/-- Joint smoothness holds at radius zero, including the actual poles. -/
theorem poleFamily_smooth (p : sphere (0 : E) 1) (eps : ℝ) (heps : eps^2=1) :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ,ℝ)) (𝓡 (n+1)) ∞ (poleFamily p eps heps) := by
  have hy : ContMDiff ((𝓡 n).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,E) ∞
      (fun q : PolarDir p × ℝ => ((q.1 : (ℝ ∙ (p : E))ᗮ) : E)) :=
    ((Submodule.subtypeL (ℝ ∙ (p : E))ᗮ).contMDiff.comp contMDiff_coe_sphere).comp contMDiff_fst
  have hr : ContMDiff ((𝓡 n).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞
      (fun q : PolarDir p × ℝ => q.2) := contMDiff_snd
  have ha : ContMDiff ((𝓡 n).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,E) ∞ (poleAmbient p eps) :=
    (cotAngularScale_smooth.contMDiff.comp hr).smul (contMDiff_const.add (hr.smul hy))
  exact ha.codRestrict_sphere _

def polePullback (p : sphere (0 : E) 1) (eps : ℝ) (heps : eps^2=1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) :
    C^∞⟮(𝓡 n).prod 𝓘(ℝ,ℝ), PolarDir p × ℝ; ℝ⟯ :=
  ⟨fun q => u (poleFamily p eps heps q),u.contMDiff.comp (poleFamily_smooth p eps heps)⟩

def poleMean (p : sphere (0 : E) 1) (eps : ℝ) (heps : eps^2=1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) : ℝ → ℝ :=
  angularMean (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) (polePullback p eps heps u)

theorem poleMean_smooth (p : sphere (0 : E) 1) (eps : ℝ) (heps : eps^2=1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) :
    ContDiff ℝ ∞ (poleMean p eps heps u) := angularMean_smooth _ _

private theorem angular_antipodal_integral (p : sphere (0 : E) 1) (f : PolarDir p → ℝ) :
    (∫ y, f (sphereDiffeo (n := n) (LinearIsometryEquiv.neg ℝ) y)
      ∂riemannianVolumeMeasure (𝓡 n) (PolarDir p)
        (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))) =
      ∫ y, f y ∂riemannianVolumeMeasure (𝓡 n) (PolarDir p)
        (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) := by
  let h := roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)
  let μ := riemannianVolumeMeasure (𝓡 n) (PolarDir p) h
  let φ := sphereDiffeo (E := (ℝ ∙ (p : E))ᗮ) (n := n) (LinearIsometryEquiv.neg ℝ)
  have hm : μ=Measure.map (φ.symm : PolarDir p → PolarDir p) μ := by
    have hh := riemannianVolumeMeasure_pullback h φ
    rw [pullbackMetric_round_eq] at hh
    exact hh
  have hp : MeasurePreserving (φ.symm : PolarDir p → PolarDir p) μ μ :=
    ⟨φ.symm.continuous.measurable,hm.symm⟩
  have heq : (φ.symm : PolarDir p → PolarDir p) = φ := by
    funext y
    apply Subtype.ext
    change (LinearIsometryEquiv.neg ℝ).symm (y : (ℝ ∙ (p : E))ᗮ)=
      (LinearIsometryEquiv.neg ℝ) (y : (ℝ ∙ (p : E))ᗮ)
    rfl
  rw [← heq]
  exact hp.integral_comp φ.symm.toHomeomorph.measurableEmbedding f

/-- The genuine antipodal angular substitution proves evenness of the
pole-radius average; no symmetry of the input sphere function is assumed. -/
theorem poleMean_even (p : sphere (0 : E) 1) (eps : ℝ) (heps : eps^2=1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) :
    Function.Even (poleMean p eps heps u) := by
  intro r
  unfold poleMean angularMean
  congr 1
  have heq : (fun y : PolarDir p => polePullback p eps heps u (y,-r)) =
      fun y => polePullback p eps heps u
        (sphereDiffeo (n := n) (LinearIsometryEquiv.neg ℝ) y,r) := by
    funext y
    apply congrArg u
    apply Subtype.ext
    change cotAngularScale (-r) • (eps • (p : E)+(-r) • ((y : (ℝ ∙ (p : E))ᗮ) : E)) =
      cotAngularScale r • (eps • (p : E)+r • (-((y : (ℝ ∙ (p : E))ᗮ) : E)))
    simp only [cotAngularScale,neg_sq,neg_smul,smul_neg]
  rw [heq]
  exact angular_antipodal_integral p (fun y => polePullback p eps heps u (y,r))

theorem cotAngularScale_inverse_radius (eps r : ℝ) (heps : eps^2=1) (hr : 0<r) :
    cotAngularScale (eps/r)=r*cotAngularScale r := by
  have hs : cotAngularScale (eps/r)^2=(r*cotAngularScale r)^2 := by
    unfold cotAngularScale
    rw [mul_pow,inv_pow,inv_pow,Real.sq_sqrt (by positivity : 0≤1+(eps/r)^2),
      Real.sq_sqrt (by positivity : 0≤1+r^2)]
    field_simp
    nlinarith [heps]
  nlinarith [cotAngularScale_pos (eps/r),mul_pos hr (cotAngularScale_pos r)]

omit [FiniteDimensional ℝ E] in
/-- The original cot angular average and the normalized pole-radius
average evaluate exactly the same actual sphere points. -/
theorem poleFamily_eq_cot (p : sphere (0 : E) 1) (eps : ℝ) (heps : eps^2=1)
    (r : ℝ) (hr : 0<r) (y : PolarDir p) :
    poleFamily p eps heps (y,r)=cotSpherePD (n := n) p (y,eps/r) := by
  apply Subtype.ext
  rw [cotSpherePD_ambient]
  change cotAngularScale r • (eps • (p : E)+r • ((y : (ℝ ∙ (p : E))ᗮ) : E)) = _
  rw [cotAngularScale_inverse_radius eps r heps hr]
  have hc : r*cotAngularScale r*(eps/r)=cotAngularScale r*eps := by
    field_simp
  simp only [smul_add,smul_smul]
  rw [hc,mul_comm r (cotAngularScale r)]

theorem poleMean_eq_cotMean (p : sphere (0 : E) 1) (eps : ℝ) (heps : eps^2=1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) (hr : 0<r) :
    poleMean p eps heps u r=cotMean p u (eps/r) := by
  unfold poleMean cotMean angularMean
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  exact congrArg u (poleFamily_eq_cot p eps heps r hr y)

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E=n+2)] in
private theorem polarNonempty (p : sphere (0 : E) 1) (hn : finrank ℝ E=n+2) : Nonempty (PolarDir p) := by
  let : Fact (finrank ℝ E=n+2) := ⟨hn⟩
  let : Nontrivial (ℝ ∙ (p : E))ᗮ :=
    Module.nontrivial_of_finrank_eq_succ (polarDir_finrank (n := n) p)
  obtain ⟨y,hy⟩ := (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1) :
    (sphere (0 : (ℝ ∙ (p : E))ᗮ) 1).Nonempty)
  exact ⟨⟨y,hy⟩⟩

def polePoint (p : sphere (0 : E) 1) (eps : ℝ) (heps : eps^2=1) : sphere (0 : E) 1 :=
  ⟨eps • (p : E),by
    rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,norm_eq_of_mem_sphere p,mul_one]
    nlinarith [abs_nonneg eps,sq_abs eps]⟩

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E=n+2)] in
theorem poleFamily_zero (p : sphere (0 : E) 1) (eps : ℝ) (heps : eps^2=1) (y : PolarDir p) :
    poleFamily p eps heps (y,0)=polePoint p eps heps := by
  apply Subtype.ext
  simp only [poleFamily,polePoint,poleAmbient,cotAngularScale,zero_pow (by decide : 2≠0),
    add_zero,Real.sqrt_one,inv_one,zero_smul,one_smul]

theorem poleMean_zero (p : sphere (0 : E) 1) (eps : ℝ) (heps : eps^2=1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) :
    poleMean p eps heps u 0=u (polePoint p eps heps) := by
  let _ : Nonempty (PolarDir p) := polarNonempty p (Fact.out : finrank ℝ E=n+2)
  change (∫ y : PolarDir p, u (poleFamily p eps heps (y,0))
    ∂riemannianVolumeMeasure (𝓡 n) (PolarDir p) (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)))/
      angularVolume (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))=u (polePoint p eps heps)
  simp_rw [poleFamily_zero]
  rw [integral_const,smul_eq_mul]
  exact mul_div_cancel_left₀ _ (angularVolume_pos _).ne'

end DFLMeanSphere
