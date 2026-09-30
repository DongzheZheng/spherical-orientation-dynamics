import continuation.CotAngularProjection
import continuation.CotAngularCoercivity
import continuation.RoundAngularDeviationPoincare

/-! Genuine global coercivity of the original angular mean complement.
The complement is an actual smooth product state, and no global sphere
extension or zero-angular-mean assumption is made. Finite sphere energy
implies true integrability of its energy and centrifugal penalty. -/
noncomputable section
set_option maxHeartbeats 1000000
open Bundle Manifold MeasureTheory Set Filter Metric Module
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

/-- The actual weighted product Dirichlet energy density of the transverse
angular complement. -/
def cotDeviationEnergy (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) : ℝ :=
  (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
    (∫ y : PolarDir p, normGradSqFun (cotProductMetric (n := n) p)
      (cotDeviation p u) (y,s) ∂cotAngularVolume (n := n) p)

/-- The original first-mode centrifugal penalty for the actual transverse
projection, with its genuine physical weight. -/
def cotDeviationPenalty (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) : ℝ :=
  (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
    ((cotAngularScale s^2)⁻¹*(n : ℝ))*
      (∫ y : PolarDir p, (cotDeviation p u (y,s))^2 ∂cotAngularVolume (n := n) p)

private theorem cotDensity_nonneg (r s : ℝ) :
    0 ≤ cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)) :=
  (mul_pos (mul_pos (pow_pos (cotAngularScale_pos s) n) (cotLineScale_pos s))
    (Real.exp_pos _)).le

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = n + 2)] in
private theorem cotDensity_continuous (r : ℝ) (p : sphere (0 : E) 1) :
    Continuous (fun q : PolarDir p × ℝ =>
      cotAngularScale q.2^n*cotLineScale q.2*Real.exp (r*(q.2*cotAngularScale q.2))) := by
  have hA : Continuous (fun q : PolarDir p × ℝ => cotAngularScale q.2) :=
    cotAngularScale_smooth.continuous.comp continuous_snd
  have hB : Continuous (fun q : PolarDir p × ℝ => cotLineScale q.2) :=
    cotLineScale_smooth.continuous.comp continuous_snd
  exact ((hA.pow n).mul hB).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_snd.mul hA)))

private theorem cotAngularIntegral_aestronglyMeasurable (p : sphere (0 : E) 1)
    (K : PolarDir p × ℝ → ℝ) (hK : Continuous K) :
    AEStronglyMeasurable (fun s : ℝ => ∫ y : PolarDir p, K (y,s)
      ∂cotAngularVolume (n := n) p) volume := by
  let _ : SigmaFinite (cotAngularVolume (n := n) p) := riemannianVolumeMeasure_sigmaFinite _
  have hSM : @StronglyMeasurable (PolarDir p × ℝ) ℝ _
      (@Prod.instMeasurableSpace (PolarDir p) ℝ _ _) K := by
    rw [@BorelSpace.measurable_eq (PolarDir p × ℝ) _
      (@Prod.instMeasurableSpace (PolarDir p) ℝ _ _) Prod.borelSpace]
    exact hK.stronglyMeasurable
  exact (hSM.integral_prod_left' (μ := cotAngularVolume (n := n) p)).aestronglyMeasurable

private theorem cot_deviation_product_energy_formula (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (s : ℝ) :
    (∫ y : PolarDir p, normGradSqFun (cotProductMetric (n := n) p)
      (cotDeviation p u) (y,s) ∂cotAngularVolume (n := n) p) =
      (cotAngularScale s^2)⁻¹*(∫ y : PolarDir p,
        normGradSqFun (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))
          (fun z : PolarDir p => cotDeviation p u (z,s)) y ∂cotAngularVolume (n := n) p)+
      (cotLineScale s^2)⁻¹*(∫ y : PolarDir p,
        (deriv (fun t : ℝ => cotDeviation p u (y,t)) s)^2 ∂cotAngularVolume (n := n) p) := by
  let gA := roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)
  let δ := cotDeviation p u
  let _ : IsFiniteMeasure (cotAngularVolume (n := n) p) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace gA
  have hFs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y : PolarDir p => δ (y,s)) :=
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
  have hid : (fun y : PolarDir p => normGradSqFun (cotProductMetric (n := n) p) δ (y,s)) =
      fun y : PolarDir p => (cotAngularScale s^2)⁻¹*normGradSqFun gA (fun z => δ (z,s)) y+
        (cotLineScale s^2)⁻¹*(deriv (fun t : ℝ => δ (y,t)) s)^2 := by
    funext y
    exact DFLProductSlices.separated_gradient_energy_slices gA (cotProductMetric (n := n) p)
      cotAngularScale cotLineScale cotAngularScale_pos cotLineScale_pos
      (cotProductMetric_separated p) δ (y,s)
  rw [hid,integral_add (hA.const_mul _) (hD.const_mul _),integral_const_mul,integral_const_mul]

/-- At every height the genuine transverse product energy is no greater
than the original sphere energy. The removed radial mean energy is nonnegative. -/
theorem cot_deviation_slice_energy_lower (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) :
    cotDeviationEnergy p u r s ≤ ∫ y : PolarDir p,
      (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
        normGradSqFun (roundMetric (E := E) (n := n+1)) u
          (cotSpherePD (n := n) p (y,s)) ∂cotAngularVolume (n := n) p := by
  let _ : Nonempty (PolarDir p) := polarNonempty (n := n) p
  rw [integral_const_mul]
  unfold cotDeviationEnergy
  apply mul_le_mul_of_nonneg_left _ (cotDensity_nonneg (n := n) r s)
  have hid : (fun y : PolarDir p => normGradSqFun (roundMetric (E := E) (n := n+1)) u
      (cotSpherePD (n := n) p (y,s))) = fun y =>
      normGradSqFun (cotProductMetric (n := n) p) (cotSpherePullback p u) (y,s) := by
    funext y
    exact (cotSpherePD_normGradSq p u (y,s)).symm
  rw [hid,cot_deviation_product_energy_formula]
  rw [DFLSeparatedMean.separated_angular_mean_energy
    (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)) (cotProductMetric (n := n) p)
    cotAngularScale cotLineScale cotAngularScale_pos cotLineScale_pos
    (cotProductMetric_separated p) (cotSpherePullback p u) s]
  simp only [cotDeviation,cotAngularVolume]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sq_nonneg _))
  apply le_add_of_nonneg_left
  exact mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)

private theorem cot_deviation_full_slice_integrable (p : sphere (0 : E) 1)
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


private theorem cotDeviationEnergy_nonneg (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) :
    0 ≤ cotDeviationEnergy p u r s := by
  unfold cotDeviationEnergy
  exact mul_nonneg (cotDensity_nonneg (n := n) r s)
    (integral_nonneg (fun _ => normGradSqFun_nonneg _ _ _))

/-- True global transverse Dirichlet integrability, including both poles,
is derived from the original compact sphere energy. -/
theorem cot_deviation_energy_integrable (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    Integrable (cotDeviationEnergy p u r) volume := by
  have hSM := cotAngularIntegral_aestronglyMeasurable (n := n) p
    (fun q : PolarDir p × ℝ =>
      (cotAngularScale q.2^n*cotLineScale q.2*Real.exp (r*(q.2*cotAngularScale q.2)))*
        normGradSqFun (cotProductMetric (n := n) p) (cotDeviation p u) q)
    ((cotDensity_continuous (n := n) r p).mul
      (normGradSqFun_continuous _ (cotDeviation p u).contMDiff))
  have hSM' : AEStronglyMeasurable (cotDeviationEnergy p u r) volume := by
    change AEStronglyMeasurable (fun s : ℝ => cotDeviationEnergy p u r s) volume
    simpa only [cotDeviationEnergy,integral_const_mul] using hSM
  apply (cot_deviation_full_slice_integrable p u r).mono' hSM'
  filter_upwards [] with s
  rw [Real.norm_eq_abs,abs_of_nonneg (cotDeviationEnergy_nonneg p u r s)]
  exact cot_deviation_slice_energy_lower p u r s

/-- The actual transverse total weighted energy is bounded by the actual
original full-sphere weighted Dirichlet energy. -/
theorem cot_weighted_deviation_energy_lower (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    (∫ s : ℝ, cotDeviationEnergy p u r s) ≤
      ∫ x : sphere (0 : E) 1, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*
        normGradSqFun (roundMetric (E := E) (n := n+1)) u x
        ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
          (roundMetric (E := E) (n := n+1)) := by
  rw [cot_sphere_integral_axial_weight_continuous (n := n) p r _
    (normGradSqFun_continuous _ u.contMDiff)]
  exact integral_mono (cot_deviation_energy_integrable p u r)
    (cot_deviation_full_slice_integrable p u r) (cot_deviation_slice_energy_lower p u r)

/-- The first angular centrifugal penalty is controlled by the true
transverse product energy at every height, without a mean-zero premise. -/
theorem cot_deviation_penalty_slice_lower (hn : 1 ≤ n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) :
    cotDeviationPenalty p u r s ≤ cotDeviationEnergy p u r s := by
  have hP := DFLGenericRound.round_product_slice_poincare
    (E := (ℝ ∙ (p : E))ᗮ) (n := n) hn (cotDeviation p u) s
    (cotDeviation_mean_zero p u s)
  have hPs := mul_le_mul_of_nonneg_left hP
    (inv_nonneg.mpr (sq_nonneg (cotAngularScale s)))
  have hBase : ((cotAngularScale s^2)⁻¹*(n : ℝ))*
      (∫ y : PolarDir p, (cotDeviation p u (y,s))^2 ∂cotAngularVolume (n := n) p) ≤
      ∫ y : PolarDir p, normGradSqFun (cotProductMetric (n := n) p)
        (cotDeviation p u) (y,s) ∂cotAngularVolume (n := n) p := by
    rw [cot_deviation_product_energy_formula]
    apply (show ((cotAngularScale s^2)⁻¹*(n : ℝ))*
      (∫ y : PolarDir p, (cotDeviation p u (y,s))^2 ∂cotAngularVolume (n := n) p) ≤
      (cotAngularScale s^2)⁻¹*(∫ y : PolarDir p,
        normGradSqFun (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))
          (fun z : PolarDir p => cotDeviation p u (z,s)) y ∂cotAngularVolume (n := n) p)
      from by simpa only [mul_assoc] using hPs).trans
    exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
      (integral_nonneg (fun _ => sq_nonneg _)))
  simpa only [cotDeviationPenalty,cotDeviationEnergy,mul_assoc] using
    mul_le_mul_of_nonneg_left hBase (cotDensity_nonneg (n := n) r s)

private theorem cotDeviationPenalty_nonneg (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) :
    0 ≤ cotDeviationPenalty p u r s := by
  unfold cotDeviationPenalty
  exact mul_nonneg (mul_nonneg (cotDensity_nonneg (n := n) r s)
    (mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (Nat.cast_nonneg n)))
    (integral_nonneg (fun _ => sq_nonneg _))

/-- The singular centrifugal penalty of the actual projected transverse
state is genuinely integrable; no global extension is assumed. -/
theorem cot_deviation_penalty_integrable (hn : 1 ≤ n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    Integrable (cotDeviationPenalty p u r) volume := by
  have hA : Continuous (fun q : PolarDir p × ℝ => cotAngularScale q.2) :=
    cotAngularScale_smooth.continuous.comp continuous_snd
  have hInv := (hA.pow 2).inv₀ (fun q => pow_ne_zero 2 (ne_of_gt (cotAngularScale_pos q.2)))
  have hC : Continuous (fun q : PolarDir p × ℝ =>
      (cotAngularScale q.2^n*cotLineScale q.2*Real.exp (r*(q.2*cotAngularScale q.2)))*
        ((cotAngularScale q.2^2)⁻¹*(n : ℝ))*(cotDeviation p u q)^2) :=
    ((cotDensity_continuous (n := n) r p).mul (hInv.mul_const (n : ℝ))).mul
      ((cotDeviation p u).contMDiff.continuous.pow 2)
  have hSM := cotAngularIntegral_aestronglyMeasurable (n := n) p _ hC
  have hSM' : AEStronglyMeasurable (cotDeviationPenalty p u r) volume := by
    change AEStronglyMeasurable (fun s : ℝ => cotDeviationPenalty p u r s) volume
    simpa only [cotDeviationPenalty,integral_const_mul] using hSM
  apply (cot_deviation_energy_integrable p u r).mono' hSM'
  filter_upwards [] with s
  rw [Real.norm_eq_abs,abs_of_nonneg (cotDeviationPenalty_nonneg p u r s)]
  exact cot_deviation_penalty_slice_lower hn p u r s

/-- Integrated true first angular penalty is dominated by transverse energy. -/
theorem cot_deviation_penalty_le_energy (hn : 1 ≤ n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    (∫ s : ℝ, cotDeviationPenalty p u r s) ≤ ∫ s : ℝ, cotDeviationEnergy p u r s :=
  integral_mono (cot_deviation_penalty_integrable hn p u r)
    (cot_deviation_energy_integrable p u r) (cot_deviation_penalty_slice_lower hn p u r)

/-- Genuine original full-sphere energy controls its automatically projected
transverse centrifugal term, with no zero-angular-mean hypothesis. -/
theorem cot_weighted_energy_deviation_centrifugal_lower (hn : 1 ≤ n)
    (p : sphere (0 : E) 1) (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    (∫ s : ℝ, cotDeviationPenalty p u r s) ≤
      ∫ x : sphere (0 : E) 1, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*
        normGradSqFun (roundMetric (E := E) (n := n+1)) u x
        ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
          (roundMetric (E := E) (n := n+1)) :=
  (cot_deviation_penalty_le_energy hn p u r).trans (cot_weighted_deviation_energy_lower p u r)

/-- The actual latitude derivative part of the projected transverse energy. -/
def cotDeviationHeightEnergy (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) : ℝ :=
  (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*
    (cotLineScale s^2)⁻¹*(∫ y : PolarDir p,
      (deriv (fun t : ℝ => cotDeviation p u (y,t)) s)^2 ∂cotAngularVolume (n := n) p)

/-- The complete original first-angular-mode lower form: genuine latitude
energy plus the centrifugal penalty of the actual transverse state. -/
def cotDeviationReducedEnergy (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) : ℝ :=
  cotDeviationPenalty p u r s+cotDeviationHeightEnergy p u r s

private theorem cotDeviationHeightEnergy_nonneg (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) :
    0 ≤ cotDeviationHeightEnergy p u r s := by
  unfold cotDeviationHeightEnergy
  exact mul_nonneg (mul_nonneg (cotDensity_nonneg (n := n) r s)
    (inv_nonneg.mpr (sq_nonneg _))) (integral_nonneg (fun _ => sq_nonneg _))

/-- True latitude derivative energy is bounded by the complete transverse
energy on every physical slice. -/
theorem cot_deviation_height_slice_lower (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) :
    cotDeviationHeightEnergy p u r s ≤ cotDeviationEnergy p u r s := by
  unfold cotDeviationHeightEnergy cotDeviationEnergy
  rw [cot_deviation_product_energy_formula]
  have hA : 0 ≤ (cotAngularScale s^2)⁻¹*(∫ y : PolarDir p,
      normGradSqFun (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))
        (fun z : PolarDir p => cotDeviation p u (z,s)) y ∂cotAngularVolume (n := n) p) :=
    mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
      (integral_nonneg (fun _ => normGradSqFun_nonneg _ _ _))
  have h := mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left (a := (cotLineScale s^2)⁻¹*(∫ y : PolarDir p,
      (deriv (fun t : ℝ => cotDeviation p u (y,t)) s)^2 ∂cotAngularVolume (n := n) p)) hA)
    (cotDensity_nonneg (n := n) r s)
  simpa only [mul_assoc] using h

/-- The true transverse latitude derivative energy is genuinely integrable
at both polar limits, by domination with actual sphere energy. -/
theorem cot_deviation_height_energy_integrable (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    Integrable (cotDeviationHeightEnergy p u r) volume := by
  have hB : Continuous (fun q : PolarDir p × ℝ => cotLineScale q.2) :=
    cotLineScale_smooth.continuous.comp continuous_snd
  have hInv := (hB.pow 2).inv₀ (fun q => pow_ne_zero 2 (ne_of_gt (cotLineScale_pos q.2)))
  have hDc : Continuous (fun q : PolarDir p × ℝ =>
      deriv (fun t : ℝ => cotDeviation p u (q.1,t)) q.2) :=
    (contMDiff_partial_deriv_snd (𝓡 n) (cotDeviation p u)).continuous
  have hC : Continuous (fun q : PolarDir p × ℝ =>
      (cotAngularScale q.2^n*cotLineScale q.2*Real.exp (r*(q.2*cotAngularScale q.2)))*
        (cotLineScale q.2^2)⁻¹*(deriv (fun t : ℝ => cotDeviation p u (q.1,t)) q.2)^2) :=
    ((cotDensity_continuous (n := n) r p).mul hInv).mul (hDc.pow 2)
  have hSM := cotAngularIntegral_aestronglyMeasurable (n := n) p _ hC
  have hSM' : AEStronglyMeasurable (cotDeviationHeightEnergy p u r) volume := by
    change AEStronglyMeasurable (fun s : ℝ => cotDeviationHeightEnergy p u r s) volume
    simpa only [cotDeviationHeightEnergy,integral_const_mul] using hSM
  apply (cot_deviation_energy_integrable p u r).mono' hSM'
  filter_upwards [] with s
  rw [Real.norm_eq_abs,abs_of_nonneg (cotDeviationHeightEnergy_nonneg p u r s)]
  exact cot_deviation_height_slice_lower p u r s

/-- The complete original first angular lower form retains the actual
latitude energy instead of discarding it. -/
theorem cot_deviation_reduced_slice_lower (hn : 1 ≤ n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r s : ℝ) :
    cotDeviationReducedEnergy p u r s ≤ cotDeviationEnergy p u r s := by
  have hP := DFLGenericRound.round_product_slice_poincare
    (E := (ℝ ∙ (p : E))ᗮ) (n := n) hn (cotDeviation p u) s
    (cotDeviation_mean_zero p u s)
  have hPs := mul_le_mul_of_nonneg_left hP
    (inv_nonneg.mpr (sq_nonneg (cotAngularScale s)))
  have htotal := add_le_add_left hPs
    ((cotLineScale s^2)⁻¹*(∫ y : PolarDir p,
      (deriv (fun t : ℝ => cotDeviation p u (y,t)) s)^2 ∂cotAngularVolume (n := n) p))
  have h := mul_le_mul_of_nonneg_left htotal (cotDensity_nonneg (n := n) r s)
  simpa only [cotDeviationReducedEnergy,cotDeviationPenalty,cotDeviationHeightEnergy,
    cotDeviationEnergy,cot_deviation_product_energy_formula,mul_add,mul_assoc] using h

/-- The entire original centrifugal-plus-latitude lower form is a true
integrable function, with no assumed endpoint control. -/
theorem cot_deviation_reduced_energy_integrable (hn : 1 ≤ n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    Integrable (cotDeviationReducedEnergy p u r) volume :=
  (cot_deviation_penalty_integrable hn p u r).add (cot_deviation_height_energy_integrable p u r)

/-- The actual full original weighted sphere energy controls the complete
first angular lower form of its true projected complement. -/
theorem cot_weighted_energy_deviation_reduced_lower (hn : 1 ≤ n)
    (p : sphere (0 : E) 1) (u : C^∞⟮𝓡 (n+1), sphere (0 : E) 1; ℝ⟯) (r : ℝ) :
    (∫ s : ℝ, cotDeviationReducedEnergy p u r s) ≤
      ∫ x : sphere (0 : E) 1, Real.exp (r*⟪(p : E),(x : E)⟫_ℝ)*
        normGradSqFun (roundMetric (E := E) (n := n+1)) u x
        ∂riemannianVolumeMeasure (𝓡 (n+1)) (sphere (0 : E) 1)
          (roundMetric (E := E) (n := n+1)) :=
  (integral_mono (cot_deviation_reduced_energy_integrable hn p u r)
    (cot_deviation_energy_integrable p u r) (cot_deviation_reduced_slice_lower hn p u r)).trans
      (cot_weighted_deviation_energy_lower p u r)

end DFLCotSphere
