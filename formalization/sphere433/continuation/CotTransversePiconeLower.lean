import continuation.CotScalarCutoff

/-! The manuscript's original transverse lower bound for the actual angular
mean complement of every true smooth full-sphere state. Scalar finite-energy
Picone is applied to almost every actual angular fiber by genuine Fubini. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold MeasureTheory Set Filter Metric Module Function
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DFLAngularMean
namespace DFLCotSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E = n + 2)]
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p) := borel (PolarDir p)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p) := ⟨rfl⟩
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p × ℝ) := borel (PolarDir p × ℝ)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p × ℝ) := ⟨rfl⟩
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

include n in
omit [FiniteDimensional ℝ E] in
private theorem polarNonempty (p : sphere (0 : E) 1) : Nonempty (PolarDir p) := by
  let _ : Nontrivial (ℝ ∙ (p : E))ᗮ :=
    Module.nontrivial_of_finrank_eq_succ (polarDir_finrank (n := n) p)
  exact (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)).coe_sort

def cotTransverseScalarMass (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) (q : PolarDir p × ℝ) : ℝ :=
  cotScalarMass n r (fun s => cotDeviation p u (q.1,s)) q.2

def cotTransverseScalarReduced (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) (q : PolarDir p × ℝ) : ℝ :=
  cotScalarReducedForm n r (fun s => cotDeviation p u (q.1,s)) q.2

def cotTransverseMass (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) : ℝ :=
  ∫ y : PolarDir p, cotTransverseScalarMass p u r (y,s) ∂cotAngularVolume (n := n) p

def cotTransverseReduced (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) : ℝ :=
  ∫ y : PolarDir p, cotTransverseScalarReduced p u r (y,s) ∂cotAngularVolume (n := n) p

private theorem cotTransverseScalarMass_continuous (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    Continuous (cotTransverseScalarMass p u r) :=
  ((cotScalarDensity_continuous n r).comp continuous_snd).mul
    ((cotDeviation p u).contMDiff.continuous.pow 2)

private theorem cotTransverseScalarReduced_continuous (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    Continuous (cotTransverseScalarReduced p u r) := by
  have hD : Continuous (fun q : PolarDir p × ℝ =>
      deriv (fun s : ℝ => cotDeviation p u (q.1,s)) q.2) :=
    (contMDiff_partial_deriv_snd (𝓡 n) (cotDeviation p u)).continuous
  exact ((cotScalarDensity_continuous n r).comp continuous_snd).mul
    (((((cotLineScale_smooth.continuous.pow 2).inv₀
      (fun s => pow_ne_zero 2 (ne_of_gt (cotLineScale_pos s)))).comp continuous_snd).mul (hD.pow 2)).add
      (((cotScalarCentrifugal_continuous n).comp continuous_snd).mul
        ((cotDeviation p u).contMDiff.continuous.pow 2)))

omit [FiniteDimensional ℝ E] in
private theorem cotKernel_stronglyMeasurable (p : sphere (0 : E) 1)
    (K : PolarDir p × ℝ → ℝ) (hK : Continuous K) :
    @StronglyMeasurable (PolarDir p × ℝ) ℝ _
      (@Prod.instMeasurableSpace (PolarDir p) ℝ _ _) K := by
  rw [@BorelSpace.measurable_eq (PolarDir p × ℝ) _
    (@Prod.instMeasurableSpace (PolarDir p) ℝ _ _) Prod.borelSpace]
  exact hK.stronglyMeasurable

private theorem cotKernel_integrable (p : sphere (0 : E) 1)
    (K : PolarDir p × ℝ → ℝ) (hK : Continuous K) (hNonneg : ∀ q, 0 ≤ K q)
    (hOuter : Integrable (fun s : ℝ => ∫ y : PolarDir p, K (y,s)
      ∂cotAngularVolume (n := n) p) volume) :
    @MeasureTheory.Integrable ℝ _ _ (PolarDir p × ℝ)
      (@Prod.instMeasurableSpace (PolarDir p) ℝ _ _) K
      ((cotAngularVolume (n := n) p).prod volume) := by
  let _ : SigmaFinite (cotAngularVolume (n := n) p) := riemannianVolumeMeasure_sigmaFinite _
  let _ : IsFiniteMeasure (cotAngularVolume (n := n) p) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace _
  have hSM := (cotKernel_stronglyMeasurable p K hK).aestronglyMeasurable
    (μ := (cotAngularVolume (n := n) p).prod volume)
  apply (integrable_prod_iff' hSM).2
  constructor
  · filter_upwards [] with s
    exact (hK.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · have hNorm : (fun s : ℝ => ∫ y : PolarDir p, ‖K (y,s)‖ ∂cotAngularVolume (n := n) p) =
        fun s : ℝ => ∫ y : PolarDir p, K (y,s) ∂cotAngularVolume (n := n) p := by
      funext s
      apply integral_congr_ae
      filter_upwards [] with y
      exact Real.norm_of_nonneg (hNonneg (y,s))
    rw [hNorm]
    exact hOuter

private theorem cot_transverse_full_mass_slice_integrable (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    Integrable (fun s : ℝ => ∫ y : PolarDir p,
      (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
        (u (cotSpherePD (n := n) p (y,s)))^2 ∂cotAngularVolume (n := n) p) volume := by
  let F : sphere (0 : E) 1 → ℝ := fun x =>
    Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*(u x)^2
  have hFC : Continuous F :=
    (Real.continuous_exp.comp (continuous_const.mul
      (continuous_const.inner continuous_subtype_val))).mul
        (u.contMDiff.continuous.pow 2)
  let _ : IsFiniteMeasure (riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
    (roundMetric (E := E) (n := n+1))) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace _
  have hI : Integrable F (riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
      (roundMetric (E := E) (n := n+1))) :=
    hFC.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hphi := (cotSpherePD_smooth (n := n) p).continuous.measurable
  have hIm : Integrable F (Measure.map (cotSpherePD (n := n) p)
      (riemannianVolumeMeasure ((𝓡 n).prod 𝓘(ℝ, ℝ)) (PolarDir p × ℝ)
        (cotProductMetric (n := n) p))) := by
    rw [cotProductMetric_volume_pushforward_full]
    exact hI
  have hIp := hIm.comp_aemeasurable hphi.aemeasurable
  have hprod := (DFLSeparatedBochner.separated_integrable_product
    (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) (cotProductMetric (n := n) p)
    cotAngularScale cotLineScale cotAngularScale_pos cotLineScale_pos
    cotAngularScale_smooth.continuous cotLineScale_smooth.continuous
    (cotProductMetric_separated p) (F ∘ cotSpherePD (n := n) p)).1 hIp
  let _ : SigmaFinite (cotAngularVolume (n := n) p) :=
    riemannianVolumeMeasure_sigmaFinite _
  have houter := hprod.integral_prod_right
  simpa only [finrank_euclideanSpace,Fintype.card_fin,Function.comp_def,F,
    cotSpherePD_height,mul_assoc] using houter



private theorem cotTransverseScalarMass_nonneg (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) (q : PolarDir p × ℝ) :
    0 ≤ cotTransverseScalarMass p u r q :=
  mul_nonneg (cotScalarDensity_pos n r q.2).le (sq_nonneg _)

private theorem cotTransverseScalarReduced_nonneg (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) (q : PolarDir p × ℝ) :
    0 ≤ cotTransverseScalarReduced p u r q := by
  unfold cotTransverseScalarReduced cotScalarReducedForm cotScalarCentrifugal
  exact mul_nonneg (cotScalarDensity_pos n r q.2).le
    (add_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (inv_nonneg.mpr (sq_nonneg _))) (sq_nonneg _)))

/-- The actual transverse mass at every height is controlled by original
mass; the discarded angular-average square is nonnegative. -/
theorem cot_transverse_mass_slice_lower (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) :
    cotTransverseMass p u r s ≤ ∫ y : PolarDir p,
      (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
        (u (cotSpherePD (n := n) p (y,s)))^2 ∂cotAngularVolume (n := n) p := by
  let _ : Nonempty (PolarDir p) := polarNonempty (n := n) p
  let gA := roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)
  have hNorm : (∫ y : PolarDir p, (cotDeviation p u (y,s))^2
      ∂cotAngularVolume (n := n) p) ≤
      ∫ y : PolarDir p, (cotSpherePullback p u (y,s))^2 ∂cotAngularVolume (n := n) p := by
    have hSplit := angular_square_split gA (cotSpherePullback p u) s
    rw [hSplit]
    exact le_add_of_nonneg_left (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
  unfold cotTransverseMass cotTransverseScalarMass cotScalarMass
  dsimp only
  rw [integral_const_mul,integral_const_mul]
  exact mul_le_mul_of_nonneg_left hNorm (cotScalarDensity_pos n r s).le

/-- Actual transverse mass is genuinely integrable, including the polar
limits; no projected extension or mean constraint is required. -/
theorem cot_transverse_mass_integrable (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    Integrable (cotTransverseMass p u r) volume := by
  let _ : SigmaFinite (cotAngularVolume (n := n) p) := riemannianVolumeMeasure_sigmaFinite _
  have hSM := cotKernel_stronglyMeasurable p (cotTransverseScalarMass p u r)
    (cotTransverseScalarMass_continuous p u r)
  have hOuterSM : AEStronglyMeasurable (cotTransverseMass p u r) volume := by
    change AEStronglyMeasurable (fun s : ℝ => ∫ y : PolarDir p,
      cotTransverseScalarMass p u r (y,s) ∂cotAngularVolume (n := n) p) volume
    exact (hSM.integral_prod_left' (μ := cotAngularVolume (n := n) p)).aestronglyMeasurable
  apply (cot_transverse_full_mass_slice_integrable p u r).mono' hOuterSM
  filter_upwards [] with s
  have hNonneg : 0 ≤ cotTransverseMass p u r s :=
    integral_nonneg (fun y => cotTransverseScalarMass_nonneg p u r (y,s))
  rw [Real.norm_eq_abs,abs_of_nonneg hNonneg]
  exact cot_transverse_mass_slice_lower p u r s

/-- The iterated scalar original reduced form is exactly the previously
proved transverse centrifugal-plus-height energy density. -/
theorem cot_transverse_reduced_eq (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) :
    cotTransverseReduced p u r s = cotDeviationReducedEnergy p u r s := by
  let _ : IsFiniteMeasure (cotAngularVolume (n := n) p) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace _
  have hM : Integrable (fun y : PolarDir p => (cotDeviation p u (y,s))^2)
      (cotAngularVolume (n := n) p) :=
    (((cotDeviation p u).contMDiff.continuous.comp (continuous_id.prodMk continuous_const)).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hD : Integrable (fun y : PolarDir p => (deriv (fun t : ℝ => cotDeviation p u (y,t)) s)^2)
      (cotAngularVolume (n := n) p) :=
    (((contMDiff_partial_deriv_snd (𝓡 n) (cotDeviation p u)).continuous.comp
      (continuous_id.prodMk continuous_const)).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold cotTransverseReduced cotTransverseScalarReduced cotScalarReducedForm
  dsimp only
  rw [integral_const_mul,integral_add (hD.const_mul _) (hM.const_mul _),
    integral_const_mul,integral_const_mul]
  dsimp [cotScalarDensity,cotScalarCentrifugal,cotHeight,cotDeviationReducedEnergy,
    cotDeviationPenalty,cotDeviationHeightEnergy]
  ring

/-- Genuine product-measure transverse mass integrability. -/
theorem cot_transverse_mass_integrable_product (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    @MeasureTheory.Integrable ℝ _ _ (PolarDir p × ℝ)
      (@Prod.instMeasurableSpace (PolarDir p) ℝ _ _) (cotTransverseScalarMass p u r)
      ((cotAngularVolume (n := n) p).prod volume) :=
  cotKernel_integrable (n := n) p _ (cotTransverseScalarMass_continuous p u r)
    (cotTransverseScalarMass_nonneg p u r) (cot_transverse_mass_integrable p u r)

/-- Genuine product-measure complete transverse reduced energy integrability. -/
theorem cot_transverse_reduced_integrable_product (hn : 1 ≤ n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    @MeasureTheory.Integrable ℝ _ _ (PolarDir p × ℝ)
      (@Prod.instMeasurableSpace (PolarDir p) ℝ _ _) (cotTransverseScalarReduced p u r)
      ((cotAngularVolume (n := n) p).prod volume) := by
  have hOuter : Integrable (fun s : ℝ => ∫ y : PolarDir p,
      cotTransverseScalarReduced p u r (y,s) ∂cotAngularVolume (n := n) p) volume := by
    change Integrable (fun s : ℝ => cotTransverseReduced p u r s) volume
    simpa only [cot_transverse_reduced_eq] using (cot_deviation_reduced_energy_integrable hn p u r)
  exact cotKernel_integrable (n := n) p _ (cotTransverseScalarReduced_continuous p u r)
    (cotTransverseScalarReduced_nonneg p u r) hOuter

/-- Each actual angular fiber is a true C2 cot state, without endpoint
regularity of any divided amplitude. -/
theorem cot_deviation_real_slice_smooth (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (y : PolarDir p) :
    ContDiff ℝ 2 (fun s : ℝ => cotDeviation p u (y,s)) := by
  have h : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => cotDeviation p u (y,s)) :=
    (cotDeviation p u).contMDiff.comp (contMDiff_const.prodMk contMDiff_id)
  exact (contMDiff_iff_contDiff.mp h).of_le
    (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

/-- The actual first transverse minimum controls the entire true angular
mean complement. No angular mean constraint or projection extension is input. -/
theorem cot_transverse_first_minimum_lower (hn : 1 ≤ n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)*
      (∫ s : ℝ, cotTransverseMass p u r s) ≤ ∫ s : ℝ, cotTransverseReduced p u r s := by
  let _ : SigmaFinite (cotAngularVolume (n := n) p) := riemannianVolumeMeasure_sigmaFinite _
  have hM := cot_transverse_mass_integrable_product p u r
  have hE := cot_transverse_reduced_integrable_product hn p u r
  have hMFub := integral_integral_swap (f := fun y : PolarDir p => fun s : ℝ =>
    cotTransverseScalarMass p u r (y,s)) hM
  have hEFub := integral_integral_swap (f := fun y : PolarDir p => fun s : ℝ =>
    cotTransverseScalarReduced p u r (y,s)) hE
  change _*(∫ s : ℝ, ∫ y : PolarDir p, cotTransverseScalarMass p u r (y,s)
      ∂cotAngularVolume (n := n) p) ≤
    ∫ s : ℝ, ∫ y : PolarDir p, cotTransverseScalarReduced p u r (y,s) ∂cotAngularVolume (n := n) p
  rw [← hMFub,← hEFub,← integral_const_mul]
  apply integral_mono_ae (hM.integral_prod_left.const_mul _) hE.integral_prod_left
  filter_upwards [hM.prod_right_ae,hE.prod_right_ae] with y hyM hyE
  exact cot_scalar_first_transverse_finite_lower n hn r (fun s : ℝ => cotDeviation p u (y,s))
    (cot_deviation_real_slice_smooth p u y) hyM hyE

/-- The actual full original weighted sphere Dirichlet energy dominates
its entire transverse projected mass at the actual original first-mode
minimum. All pole closure and scalar applications have been proved. -/
theorem cot_weighted_energy_transverse_minimum_lower (hn : 1 ≤ n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)*
      (∫ s : ℝ, cotTransverseMass p u r s) ≤
      ∫ x : sphere (0 : E) 1, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*
        normGradSqFun (roundMetric (E := E) (n := n+1)) u x
        ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
          (roundMetric (E := E) (n := n+1)) := by
  apply (cot_transverse_first_minimum_lower hn p u r).trans
  have h := cot_weighted_energy_deviation_reduced_lower hn p u r
  simpa only [cot_transverse_reduced_eq] using h

/-- Exact physical transverse mass density in the actual projection split. -/
theorem cot_transverse_mass_eq (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) :
    cotTransverseMass p u r s = cotScalarDensity n r s*
      (∫ y : PolarDir p, (cotDeviation p u (y,s))^2 ∂cotAngularVolume (n := n) p) := by
  unfold cotTransverseMass cotTransverseScalarMass cotScalarMass
  dsimp only
  rw [integral_const_mul]

/-- The actual first transverse minimum controls the actual transverse total
energy itself, so it combines with the radial-mean lower bound without
losing the orthogonal energy splitting. -/
theorem cot_transverse_first_minimum_le_deviation_energy (hn : 1 ≤ n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)*
      (∫ s : ℝ, cotTransverseMass p u r s) ≤ ∫ s : ℝ, cotDeviationEnergy p u r s := by
  apply (cot_transverse_first_minimum_lower hn p u r).trans
  have h := integral_mono (cot_deviation_reduced_energy_integrable hn p u r)
    (cot_deviation_energy_integrable p u r) (cot_deviation_reduced_slice_lower hn p u r)
  simpa only [cot_transverse_reduced_eq] using h

end DFLCotSphere
