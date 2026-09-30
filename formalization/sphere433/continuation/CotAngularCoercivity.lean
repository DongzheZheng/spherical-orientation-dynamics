import continuation.CotAngularPoincare

/-! The original first angular-mode centrifugal lower term in the actual
full-sphere weighted energy. Its integrability is derived from the actual
finite smooth energy and the slice Poincare theorem, rather than assumed. -/
noncomputable section
set_option maxHeartbeats 800000
open Bundle Manifold MeasureTheory Set Filter Metric Module
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

namespace DFLCotSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E = n + 2)]
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p) := borel (PolarDir p)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p) := ⟨rfl⟩
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p × ℝ) := borel (PolarDir p × ℝ)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p × ℝ) := ⟨rfl⟩
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

omit [FiniteDimensional ℝ E] in
private theorem cotSliceMap_smooth (p : sphere (0 : E) 1) (s : ℝ) :
    ContMDiff (𝓡 n) (𝓡 (n+1)) ∞ (fun y : PolarDir p => cotSpherePD (n := n) p (y,s)) :=
  (cotSpherePD_smooth (n := n) p).comp (contMDiff_id.prodMk contMDiff_const)

/-- Slice angular coercivity is controlled by the actual complete sphere
energy density, with the true nonnegative latitude contribution retained. -/
theorem cot_angular_slice_full_energy_lower (hn : 1 ≤ n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (s : ℝ)
    (hmean : (∫ y : PolarDir p, u (cotSpherePD (n := n) p (y,s))
      ∂cotAngularVolume (n := n) p) = 0) :
    ((cotAngularScale s^2)⁻¹ * (n : ℝ))*
      (∫ y : PolarDir p, (u (cotSpherePD (n := n) p (y,s)))^2
        ∂cotAngularVolume (n := n) p) ≤
      ∫ y : PolarDir p,
        normGradSqFun (roundMetric (E := E) (n := n+1)) u
          (cotSpherePD (n := n) p (y,s)) ∂cotAngularVolume (n := n) p := by
  let _ : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := ⟨by simp; omega⟩
  let gA := roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)
  let μA := cotAngularVolume (n := n) p
  let _ : IsFiniteMeasure μA := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace gA
  have hA : Integrable (fun y : PolarDir p => (cotAngularScale s^2)⁻¹ *
      normGradSqFun gA (cotAngularSlice p u s) y) μA :=
    (continuous_const.mul (normGradSqFun_continuous gA (cotAngularSlice p u s).contMDiff)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hF : Integrable (fun y : PolarDir p =>
      normGradSqFun (roundMetric (E := E) (n := n+1)) u
        (cotSpherePD (n := n) p (y,s))) μA :=
    ((normGradSqFun_continuous _ u.contMDiff).comp (cotSliceMap_smooth p s).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply (cot_angular_slice_scaled_poincare hn p u s hmean).trans
  apply integral_mono hA hF
  intro y
  change (cotAngularScale s^2)⁻¹ *
    normGradSqFun (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))
      (fun z : PolarDir p => u (cotSpherePD (n := n) p (z,s))) y ≤
    normGradSqFun (roundMetric (E := E) (n := n+1)) u
      (cotSpherePD (n := n) p (y,s))
  rw [cotSpherePD_gradient_energy (n := n) p u (y,s)]
  exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (sq_nonneg _))

def cotAngularPenalty (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) : ℝ :=
  (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
    ((cotAngularScale s^2)⁻¹ * (n : ℝ))*
      (∫ y : PolarDir p, (u (cotSpherePD (n := n) p (y,s)))^2
        ∂cotAngularVolume (n := n) p)

private theorem cotAngularPenalty_nonneg (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) :
    0 ≤ cotAngularPenalty p u r s := by
  unfold cotAngularPenalty
  apply mul_nonneg
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg (pow_nonneg (cotAngularScale_pos s).le n)
        (cotLineScale_pos s).le) (Real.exp_pos _).le)
      (mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (Nat.cast_nonneg n))
  · exact integral_nonneg (fun _ => sq_nonneg _)

private theorem cot_weighted_full_slice_lower (hn : 1 ≤ n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ)
    (hmean : (∫ y : PolarDir p, u (cotSpherePD (n := n) p (y,s))
      ∂cotAngularVolume (n := n) p) = 0) :
    cotAngularPenalty p u r s ≤
      ∫ y : PolarDir p,
        (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
          normGradSqFun (roundMetric (E := E) (n := n+1)) u
            (cotSpherePD (n := n) p (y,s)) ∂cotAngularVolume (n := n) p := by
  rw [integral_const_mul]
  unfold cotAngularPenalty
  have hw : 0 ≤ cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)) :=
    (mul_pos (mul_pos (pow_pos (cotAngularScale_pos s) n) (cotLineScale_pos s))
      (Real.exp_pos _)).le
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (cot_angular_slice_full_energy_lower hn p u s hmean) hw

private theorem cot_weighted_full_slice_integrable (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    Integrable (fun s : ℝ => ∫ y : PolarDir p,
      (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
        normGradSqFun (roundMetric (E := E) (n := n+1)) u
          (cotSpherePD (n := n) p (y,s)) ∂cotAngularVolume (n := n) p) volume := by
  let F : sphere (0 : E) 1 → ℝ := fun x =>
    Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*normGradSqFun (roundMetric (E := E) (n := n+1)) u x
  have hFC : Continuous F :=
    (Real.continuous_exp.comp (continuous_const.mul
      (continuous_const.inner continuous_subtype_val))).mul
        (normGradSqFun_continuous _ u.contMDiff)
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

/-- The true first angular centrifugal penalty is genuinely integrable,
including both polar endpoints, whenever every actual angular mean vanishes. -/
theorem cot_angular_penalty_integrable (hn : 1 ≤ n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ)
    (hmean : ∀ s : ℝ, (∫ y : PolarDir p, u (cotSpherePD (n := n) p (y,s))
      ∂cotAngularVolume (n := n) p) = 0) :
    Integrable (cotAngularPenalty p u r) volume := by
  let _ : SigmaFinite (cotAngularVolume (n := n) p) :=
    riemannianVolumeMeasure_sigmaFinite _
  have hC : Continuous (fun q : PolarDir p × ℝ =>
      (cotAngularScale q.2^n*cotLineScale q.2*Real.exp (r*(q.2*cotAngularScale q.2)))*
        ((cotAngularScale q.2^2)⁻¹*(n : ℝ))*(u (cotSpherePD (n := n) p q))^2) := by
    have hA : Continuous (fun q : PolarDir p × ℝ => cotAngularScale q.2) :=
      cotAngularScale_smooth.continuous.comp continuous_snd
    have hB : Continuous (fun q : PolarDir p × ℝ => cotLineScale q.2) :=
      cotLineScale_smooth.continuous.comp continuous_snd
    have hW : Continuous (fun q : PolarDir p × ℝ =>
        cotAngularScale q.2^n*cotLineScale q.2*Real.exp (r*(q.2*cotAngularScale q.2))) :=
      ((hA.pow n).mul hB).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_snd.mul hA)))
    have hInv := (hA.pow 2).inv₀ (fun q => pow_ne_zero 2 (ne_of_gt (cotAngularScale_pos q.2)))
    exact (hW.mul (hInv.mul_const (n : ℝ))).mul
      ((u.contMDiff.continuous.comp (cotSpherePD_smooth (n := n) p).continuous).pow 2)
  have hSMProd : @StronglyMeasurable (PolarDir p × ℝ) ℝ _
      (@Prod.instMeasurableSpace (PolarDir p) ℝ _ _)
      (fun q : PolarDir p × ℝ =>
        (cotAngularScale q.2^n*cotLineScale q.2*Real.exp (r*(q.2*cotAngularScale q.2)))*
          ((cotAngularScale q.2^2)⁻¹*(n : ℝ))*(u (cotSpherePD (n := n) p q))^2) := by
    rw [@BorelSpace.measurable_eq (PolarDir p × ℝ) _
      (@Prod.instMeasurableSpace (PolarDir p) ℝ _ _) Prod.borelSpace]
    exact hC.stronglyMeasurable
  have hSM := hSMProd.integral_prod_left' (μ := cotAngularVolume (n := n) p)
  have hPenaltySM : AEStronglyMeasurable (cotAngularPenalty p u r) volume := by
    have hSM' := hSM.aestronglyMeasurable (μ := volume)
    change AEStronglyMeasurable (fun s : ℝ => cotAngularPenalty p u r s) volume
    simpa only [integral_const_mul,cotAngularPenalty] using hSM'
  apply (cot_weighted_full_slice_integrable p u r).mono' hPenaltySM
  filter_upwards [] with s
  rw [Real.norm_eq_abs,abs_of_nonneg (cotAngularPenalty_nonneg p u r s)]
  exact cot_weighted_full_slice_lower hn p u r s (hmean s)

/-- Actual global weighted Dirichlet energy dominates the original
first angular-mode term for every true smooth transverse state. -/
theorem cot_weighted_energy_angular_lower (hn : 1 ≤ n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ)
    (hmean : ∀ s : ℝ, (∫ y : PolarDir p, u (cotSpherePD (n := n) p (y,s))
      ∂cotAngularVolume (n := n) p) = 0) :
    (∫ s : ℝ, cotAngularPenalty p u r s ∂volume) ≤
      ∫ x : sphere (0 : E) 1, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*
        normGradSqFun (roundMetric (E := E) (n := n+1)) u x
        ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
          (roundMetric (E := E) (n := n+1)) := by
  rw [cot_sphere_integral_axial_weight_continuous (n := n) p r _
    (normGradSqFun_continuous _ u.contMDiff)]
  apply integral_mono (cot_angular_penalty_integrable hn p u r hmean)
    (cot_weighted_full_slice_integrable p u r)
  intro s
  exact cot_weighted_full_slice_lower hn p u r s (hmean s)

end DFLCotSphere
