import continuation.MeanSphereDomain
import continuation.CotAngularDeviationCoercivity

/-! The actual C² whole-sphere angular mean and its complement have the
same Dirichlet energies as the genuine cot product representatives.
The resulting orthogonal energy split includes both original poles. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open Bundle Manifold MeasureTheory Metric Module Set Filter
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Integral.Measure
open DFLCotSphere DFLAngularMean
namespace DFLMeanSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+2)]
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p) := borel (PolarDir p)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p) := ⟨rfl⟩
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p × ℝ) := borel (PolarDir p × ℝ)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p × ℝ) := ⟨rfl⟩
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

/-- The genuine smooth product representative of the actual angular mean. -/
def cotMeanProduct (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) :
    C^∞⟮(𝓡 n).prod 𝓘(ℝ,ℝ), PolarDir p × ℝ; ℝ⟯ :=
  ⟨fun q => cotMean p u q.2,
    (contMDiff_iff_contDiff.mpr (cotMean_smooth p u)).comp contMDiff_snd⟩

omit [FiniteDimensional ℝ E] in
/-- Actual C² observables need no C∞ extension to transfer their gradient
energy along the proved cot sphere diffeomorphism. -/
theorem cot_C2_normGradSq (p : sphere (0 : E) 1)
    (f : sphere (0 : E) 1 → ℝ) (hf : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) 2 f)
    (F : C^∞⟮(𝓡 n).prod 𝓘(ℝ,ℝ), PolarDir p × ℝ; ℝ⟯)
    (hF : ∀ q, f (cotSpherePD (n := n) p q)=F q) (q : PolarDir p × ℝ) :
    normGradSqFun (roundMetric (E := E) (n := n+1)) f (cotSpherePD (n := n) p q)=
      normGradSqFun (cotProductMetric (n := n) p) F q := by
  have he : f ∘ cotSpherePD (n := n) p = F := by funext z; exact hF z
  have hh := normGradSqFun_eq_of_pullback_inner (cotProductMetric (n := n) p)
    (roundMetric (E := E) (n := n+1)) (cotSpherePD (n := n) p) q
    ((cotSpherePD_smooth (n := n) p).mdifferentiableAt (by simp))
    (cotProductMetric_inner_pullback p q) (cotSpherePD_mfderiv_surjective p q) f
    (hf.mdifferentiableAt (by norm_num))
  rw [he] at hh
  exact hh.symm

/-- Actual weighted energy of a whole-sphere C² representative equals its
actual product-gradient integral. -/
theorem cot_C2_weighted_energy_product (p : sphere (0 : E) 1) (r : ℝ)
    (f : sphere (0 : E) 1 → ℝ) (hf : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) 2 f)
    (F : C^∞⟮(𝓡 n).prod 𝓘(ℝ,ℝ), PolarDir p × ℝ; ℝ⟯)
    (hF : ∀ q, f (cotSpherePD (n := n) p q)=F q) :
    (∫ x, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*
      normGradSqFun (roundMetric (E := E) (n := n+1)) f x
      ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))) =
      ∫ s : ℝ, (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
        ∫ y : PolarDir p, normGradSqFun (cotProductMetric (n := n) p) F (y,s)
          ∂cotAngularVolume (n := n) p := by
  have hc : Continuous (normGradSqFun (roundMetric (E := E) (n := n+1)) f) :=
    DFLC2WeakH1.contMDiff_two_gradient_energy_continuous _ f hf
  rw [cot_sphere_integral_axial_weight_continuous (n := n) p r _ hc]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [cot_C2_normGradSq p f hf F hF (y,s)]

/-- Integrability of the product energy is obtained from the actual finite
C² whole-sphere energy, including its two poles. -/
theorem cot_C2_weighted_product_energy_integrable (p : sphere (0 : E) 1) (r : ℝ)
    (f : sphere (0 : E) 1 → ℝ) (hf : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) 2 f)
    (F : C^∞⟮(𝓡 n).prod 𝓘(ℝ,ℝ), PolarDir p × ℝ; ℝ⟯)
    (hF : ∀ q, f (cotSpherePD (n := n) p q)=F q) :
    Integrable (fun s : ℝ =>
      (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
        ∫ y : PolarDir p, normGradSqFun (cotProductMetric (n := n) p) F (y,s)
          ∂cotAngularVolume (n := n) p) volume := by
  let K : sphere (0 : E) 1 → ℝ := fun x =>
    Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*normGradSqFun (roundMetric (E := E) (n := n+1)) f x
  have hKC : Continuous K :=
    (Real.continuous_exp.comp (continuous_const.mul
      (continuous_const.inner continuous_subtype_val))).mul
        (DFLC2WeakH1.contMDiff_two_gradient_energy_continuous _ f hf)
  let _ : IsFiniteMeasure (riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
    (roundMetric (E := E) (n := n+1))) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace _
  have hI : Integrable K (riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
      (roundMetric (E := E) (n := n+1))) :=
    hKC.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hphi := (cotSpherePD_smooth (n := n) p).continuous.measurable
  have hIm : Integrable K (Measure.map (cotSpherePD (n := n) p)
      (riemannianVolumeMeasure ((𝓡 n).prod 𝓘(ℝ,ℝ)) (PolarDir p × ℝ)
        (cotProductMetric (n := n) p))) := by
    rw [cotProductMetric_volume_pushforward_full]
    exact hI
  have hIp := hIm.comp_aemeasurable hphi.aemeasurable
  have hprod := (DFLSeparatedBochner.separated_integrable_product
    (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) (cotProductMetric (n := n) p)
    cotAngularScale cotLineScale cotAngularScale_pos cotLineScale_pos
    cotAngularScale_smooth.continuous cotLineScale_smooth.continuous
    (cotProductMetric_separated p) (K ∘ cotSpherePD (n := n) p)).1 hIp
  let _ : SigmaFinite (cotAngularVolume (n := n) p) := riemannianVolumeMeasure_sigmaFinite _
  have houter := hprod.integral_prod_right
  have he : (fun s : ℝ => ∫ y : PolarDir p,
      (cotAngularScale s^n*cotLineScale s)*K (cotSpherePD (n := n) p (y,s))
        ∂cotAngularVolume (n := n) p) = fun s : ℝ =>
      (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
        ∫ y : PolarDir p, normGradSqFun (cotProductMetric (n := n) p) F (y,s)
          ∂cotAngularVolume (n := n) p := by
    funext s
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [K]
    rw [cotSpherePD_height,cot_C2_normGradSq p f hf F hF (y,s)]
    ring
  simpa only [finrank_euclideanSpace,Fintype.card_fin,Function.comp_def,he] using houter

theorem cot_mean_product_slice_energy (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (s : ℝ) :
    (∫ y : PolarDir p, normGradSqFun (cotProductMetric (n := n) p)
      (cotMeanProduct p u) (y,s) ∂cotAngularVolume (n := n) p)=
      (cotLineScale s^2)⁻¹*angularVolume
        (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))*(deriv (cotMean p u) s)^2 := by
  have hp : (fun y : PolarDir p => normGradSqFun (cotProductMetric (n := n) p)
      (cotMeanProduct p u) (y,s)) = fun _ : PolarDir p =>
      (cotLineScale s^2)⁻¹*(deriv (cotMean p u) s)^2 := by
    funext y
    rw [DFLProductSlices.separated_gradient_energy_slices
      (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) (cotProductMetric (n := n) p)
      cotAngularScale cotLineScale cotAngularScale_pos cotLineScale_pos
      (cotProductMetric_separated p) (cotMeanProduct p u) (y,s)]
    change (cotAngularScale s^2)⁻¹*normGradSqFun
      (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) (fun _ => cotMean p u s) y+
      (cotLineScale s^2)⁻¹*(deriv (cotMean p u) s)^2=_
    simp only [normGradSqFun_def,Connection.gradFun_const,map_zero,mul_zero,zero_add]
  rw [hp,integral_const,smul_eq_mul]
  dsimp only [cotAngularVolume,angularVolume]
  ring

/-- The actual C³ latitude representative carries exactly the radial
mean part of the original weighted Dirichlet energy. -/
theorem meanSphereProfile_weighted_energy (p : sphere (0 : E) 1) (r : ℝ)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 3 v) (hvs : ∀ t∈Icc (-1 : ℝ) 1,v t=heightMean p u t) :
    (∫ x, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*
      normGradSqFun (roundMetric (E := E) (n := n+1)) (meanSphereProfile p v) x
      ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))) =
      ∫ s : ℝ, (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
        ((cotLineScale s^2)⁻¹*angularVolume
          (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))*(deriv (cotMean p u) s)^2) := by
  rw [cot_C2_weighted_energy_product p r _
    ((meanSphereProfile_contMDiff p v hv).of_le (by norm_num)) (cotMeanProduct p u)
    (fun q => meanSphereProfile_cot p u v hvs q.1 q.2)]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [cot_mean_product_slice_energy p u s]

/-- The actual C² whole-sphere complement has precisely the transverse
product energy used in the genuine Picone lower bound. -/
theorem meanSphereDeviation_weighted_energy (p : sphere (0 : E) 1) (r : ℝ)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 3 v) (hvs : ∀ t∈Icc (-1 : ℝ) 1,v t=heightMean p u t) :
    (∫ x, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*
      normGradSqFun (roundMetric (E := E) (n := n+1)) (fun x => u x-meanSphereProfile p v x) x
      ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1))) = ∫ s, cotDeviationEnergy p u r s := by
  exact cot_C2_weighted_energy_product p r _
    ((u.contMDiff.of_le (by decide : (2 : ℕ∞ω)≤(∞ : ℕ∞ω))).sub
      ((meanSphereProfile_contMDiff p v hv).of_le (by norm_num))) (cotDeviation p u)
    (fun q => by rw [meanSphereProfile_cot p u v hvs q.1 q.2]; rfl)

theorem cot_mean_deviation_slice_energy_split (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (s : ℝ) :
    (∫ y : PolarDir p, normGradSqFun (cotProductMetric (n := n) p)
      (cotSpherePullback p u) (y,s) ∂cotAngularVolume (n := n) p)=
      (∫ y : PolarDir p, normGradSqFun (cotProductMetric (n := n) p)
        (cotMeanProduct p u) (y,s) ∂cotAngularVolume (n := n) p)+
      ∫ y : PolarDir p, normGradSqFun (cotProductMetric (n := n) p)
        (cotDeviation p u) (y,s) ∂cotAngularVolume (n := n) p := by
  let _ : Nontrivial (ℝ ∙ (p : E))ᗮ :=
    Module.nontrivial_of_finrank_eq_succ (polarDir_finrank (n := n) p)
  let _ : Nonempty (PolarDir p) :=
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ)≤1)).coe_sort
  let gA := roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)
  let _ : IsFiniteMeasure (cotAngularVolume (n := n) p) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace gA
  let δ := cotDeviation p u
  have hFs : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (fun y : PolarDir p => δ (y,s)) :=
    δ.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)
  have hA : Integrable (normGradSqFun gA (fun y : PolarDir p => δ (y,s)))
      (cotAngularVolume (n := n) p) :=
    (normGradSqFun_continuous gA hFs).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hDc : Continuous (fun y : PolarDir p => deriv (fun t : ℝ => δ (y,t)) s) :=
    (contMDiff_partial_deriv_snd (𝓡 n) δ).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hD : Integrable (fun y : PolarDir p => (deriv (fun t : ℝ => δ (y,t)) s)^2)
      (cotAngularVolume (n := n) p) :=
    (hDc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hid : (fun y : PolarDir p => normGradSqFun (cotProductMetric (n := n) p) δ (y,s))=
      fun y => (cotAngularScale s^2)⁻¹*normGradSqFun gA (fun z => δ (z,s)) y+
        (cotLineScale s^2)⁻¹*(deriv (fun t : ℝ => δ (y,t)) s)^2 := by
    funext y
    exact DFLProductSlices.separated_gradient_energy_slices gA (cotProductMetric (n := n) p)
      cotAngularScale cotLineScale cotAngularScale_pos cotLineScale_pos
      (cotProductMetric_separated p) δ (y,s)
  have hsplit := DFLSeparatedMean.separated_angular_mean_energy gA (cotProductMetric (n := n) p)
    cotAngularScale cotLineScale cotAngularScale_pos cotLineScale_pos
    (cotProductMetric_separated p) (cotSpherePullback p u) s
  rw [cot_mean_product_slice_energy p u s]
  change _=_+∫ y : PolarDir p, normGradSqFun (cotProductMetric (n := n) p) δ (y,s)
    ∂cotAngularVolume (n := n) p
  rw [hid,integral_add (hA.const_mul _) (hD.const_mul _),integral_const_mul,integral_const_mul]
  dsimp only [gA,δ] at hsplit ⊢
  change _=(cotLineScale s^2)⁻¹*angularVolume _*(deriv (cotMean p u) s)^2+
    ((cotAngularScale s^2)⁻¹*(∫ y : PolarDir p, normGradSqFun _
      (fun z : PolarDir p => cotDeviation p u (z,s)) y ∂cotAngularVolume (n := n) p)+
      (cotLineScale s^2)⁻¹*(∫ y : PolarDir p, (deriv (fun t : ℝ => cotDeviation p u (y,t)) s)^2
        ∂cotAngularVolume (n := n) p))
  rw [hsplit]
  dsimp only [cotDeviation,cotMean,cotAngularVolume]
  ring

/-- Exact orthogonal Dirichlet decomposition in the genuine whole-sphere
C² form domain. Neither a global smooth deviation nor a zero-mean input
is required. -/
theorem meanSphere_weighted_energy_split (p : sphere (0 : E) 1) (r : ℝ)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 3 v) (hvs : ∀ t∈Icc (-1 : ℝ) 1,v t=heightMean p u t) :
    (∫ x, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*
      normGradSqFun (roundMetric (E := E) (n := n+1)) u x
      ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
        (roundMetric (E := E) (n := n+1)))=
      (∫ x, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*
        normGradSqFun (roundMetric (E := E) (n := n+1)) (meanSphereProfile p v) x
        ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
          (roundMetric (E := E) (n := n+1)))+
      ∫ x, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*
        normGradSqFun (roundMetric (E := E) (n := n+1)) (fun x => u x-meanSphereProfile p v x) x
        ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
          (roundMetric (E := E) (n := n+1)) := by
  have hA := cot_C2_weighted_product_energy_integrable p r _
    ((meanSphereProfile_contMDiff p v hv).of_le (by norm_num)) (cotMeanProduct p u)
    (fun q => meanSphereProfile_cot p u v hvs q.1 q.2)
  have hD := cot_C2_weighted_product_energy_integrable p r _
    ((u.contMDiff.of_le (by decide : (2 : ℕ∞ω)≤(∞ : ℕ∞ω))).sub
      ((meanSphereProfile_contMDiff p v hv).of_le (by norm_num))) (cotDeviation p u)
    (fun q => by rw [meanSphereProfile_cot p u v hvs q.1 q.2]; rfl)
  rw [cot_weighted_energy_product p r u,
    cot_C2_weighted_energy_product p r _
      ((meanSphereProfile_contMDiff p v hv).of_le (by norm_num)) (cotMeanProduct p u)
      (fun q => meanSphereProfile_cot p u v hvs q.1 q.2),
    meanSphereDeviation_weighted_energy p r u v hv hvs]
  unfold cotDeviationEnergy
  rw [← integral_add hA hD]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [cot_mean_deviation_slice_energy_split p u s,mul_add]

end DFLMeanSphere
