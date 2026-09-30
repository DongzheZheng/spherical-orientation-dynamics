import continuation.RoundPoincareEquality
import continuation.CotTransversePiconeLower

/-! The original angular equality mechanism on the actual sphere.
Vanishing of the integrated true angular defect forces sharp Poincare
equality on every latitude slice, and hence an ambient linear slice. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open Bundle Manifold MeasureTheory Metric Module Set Filter
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DFLAngularMean
namespace DFLGenericRound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+1)]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

/-- The genuine angular gradient density is represented as a smooth
function on the actual angular-sphere-times-line product. -/
def roundAngularEnergyDensity
    (F : C^∞⟮(𝓡 n).prod 𝓘(ℝ,ℝ),sphere (0 : E) 1 × ℝ;ℝ⟯) (q : sphere (0 : E) 1 × ℝ) : ℝ :=
  normGradSqFun ((roundMetric (E := E) (n := n)).prod (euclideanMetric (E := ℝ))) F q-
    (heightDerivative F q)^2

omit [FiniteDimensional ℝ E] in
theorem roundAngularEnergyDensity_eq
    (F : C^∞⟮(𝓡 n).prod 𝓘(ℝ,ℝ),sphere (0 : E) 1 × ℝ;ℝ⟯) (q : sphere (0 : E) 1 × ℝ) :
    roundAngularEnergyDensity F q=normGradSqFun (roundMetric (E := E) (n := n))
      (fun y : sphere (0 : E) 1=>F (y,q.2)) q.1 := by
  unfold roundAngularEnergyDensity
  rw [normGradSqFun_def,DFLProductSlices.product_gradient_slices,
    SmoothRiemannianMetric.prod_inner]
  change (roundMetric (E := E) (n := n)).inner q.1
      (gradFun _ (fun y : sphere (0 : E) 1=>F (y,q.2)) q.1)
      (gradFun _ (fun y : sphere (0 : E) 1=>F (y,q.2)) q.1)+
    inner ℝ (deriv (fun s : ℝ=>F (q.1,s)) q.2) (deriv (fun s : ℝ=>F (q.1,s)) q.2)-
      (deriv (fun s : ℝ=>F (q.1,s)) q.2)^2=normGradSqFun _ _ _
  rw [Real.inner_apply,normGradSqFun_def]
  ring

omit [FiniteDimensional ℝ E] in
theorem roundAngularEnergyDensity_smooth
    (F : C^∞⟮(𝓡 n).prod 𝓘(ℝ,ℝ),sphere (0 : E) 1 × ℝ;ℝ⟯) :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞ (roundAngularEnergyDensity F) :=
  (normGradSqFun_contMDiff _ F.contMDiff).sub ((heightDerivative F).contMDiff.pow 2)

theorem round_angular_slice_energy_smooth
    (F : C^∞⟮(𝓡 n).prod 𝓘(ℝ,ℝ),sphere (0 : E) 1 × ℝ;ℝ⟯) :
    ContDiff ℝ ∞ (fun s : ℝ=>∫y : sphere (0 : E) 1,
      normGradSqFun (roundMetric (E := E) (n := n)) (fun z : sphere (0 : E) 1=>F (z,s)) y
        ∂roundVolume (E := E) (n := n)) := by
  let _ : IsFiniteMeasure (roundVolume (E := E) (n := n)) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace _
  have h := contDiff_integral_of_jointContMDiff (roundVolume (E := E) (n := n))
    (fun y s=>roundAngularEnergyDensity F (y,s)) (roundAngularEnergyDensity_smooth F)
  simpa only [roundAngularEnergyDensity_eq] using h

theorem round_angular_slice_mass_smooth
    (F : C^∞⟮(𝓡 n).prod 𝓘(ℝ,ℝ),sphere (0 : E) 1 × ℝ;ℝ⟯) :
    ContDiff ℝ ∞ (fun s : ℝ=>∫y : sphere (0 : E) 1,(F (y,s))^2
      ∂roundVolume (E := E) (n := n)) := by
  let _ : IsFiniteMeasure (roundVolume (E := E) (n := n)) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace _
  exact contDiff_integral_of_jointContMDiff (roundVolume (E := E) (n := n))
    (fun y s=>(F (y,s))^2) (F.contMDiff.pow 2)

end DFLGenericRound

namespace DFLCotSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+2)]
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p) := borel (PolarDir p)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p) := ⟨rfl⟩

/-- The actual angular defect retained by the first-mode lower proof. -/
def cotAngularDefect (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1),sphere (0 : E) 1;ℝ⟯) (r s : ℝ) : ℝ :=
  (cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*(cotAngularScale s^2)⁻¹*
    ((∫y : PolarDir p,normGradSqFun (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))
      (fun z : PolarDir p=>cotDeviation p u (z,s)) y ∂cotAngularVolume (n := n) p)-
      (n : ℝ)*(∫y : PolarDir p,(cotDeviation p u (y,s))^2 ∂cotAngularVolume (n := n) p))

theorem cotAngularDefect_continuous (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1),sphere (0 : E) 1;ℝ⟯) (r : ℝ) : Continuous (cotAngularDefect p u r) := by
  have hD : Continuous (fun s : ℝ=>cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s))) :=
    ((cotAngularScale_smooth.continuous.pow n).mul cotLineScale_smooth.continuous).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.mul cotAngularScale_smooth.continuous)))
  have hI : Continuous (fun s : ℝ=>(cotAngularScale s^2)⁻¹) :=
    (cotAngularScale_smooth.continuous.pow 2).inv₀ (fun s=>pow_ne_zero 2 (cotAngularScale_pos s).ne')
  exact (hD.mul hI).mul
    ((DFLGenericRound.round_angular_slice_energy_smooth (cotDeviation p u)).continuous.sub
      (continuous_const.mul (DFLGenericRound.round_angular_slice_mass_smooth (cotDeviation p u)).continuous))

theorem cotAngularDefect_nonneg (hn : 1≤n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1),sphere (0 : E) 1;ℝ⟯) (r s : ℝ) : 0≤cotAngularDefect p u r s := by
  have h := DFLGenericRound.round_product_slice_poincare (E := (ℝ ∙ (p : E))ᗮ) (n := n)
    hn (cotDeviation p u) s (cotDeviation_mean_zero p u s)
  exact mul_nonneg (mul_nonneg
    ((mul_pos (mul_pos (pow_pos (cotAngularScale_pos s) n) (cotLineScale_pos s))
      (Real.exp_pos _)).le) (inv_nonneg.mpr (sq_nonneg _))) (sub_nonneg.mpr h)

theorem cotAngularDefect_eq_energy_sub_reduced (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1),sphere (0 : E) 1;ℝ⟯) (r s : ℝ) :
    cotAngularDefect p u r s=cotDeviationEnergy p u r s-cotDeviationReducedEnergy p u r s := by
  let gA := roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n)
  let _ : IsFiniteMeasure (cotAngularVolume (n := n) p) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace gA
  let δ := cotDeviation p u
  have hFs : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (fun y : PolarDir p=>δ (y,s)) :=
    δ.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)
  have hA : Integrable (normGradSqFun gA (fun y : PolarDir p=>δ (y,s))) (cotAngularVolume (n := n) p) :=
    (normGradSqFun_continuous gA hFs).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDc : Continuous (fun y : PolarDir p=>deriv (fun t : ℝ=>δ (y,t)) s) :=
    (contMDiff_partial_deriv_snd (𝓡 n) δ).continuous.comp (continuous_id.prodMk continuous_const)
  have hD : Integrable (fun y : PolarDir p=>(deriv (fun t : ℝ=>δ (y,t)) s)^2) (cotAngularVolume (n := n) p) :=
    (hDc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : (fun y : PolarDir p=>normGradSqFun (cotProductMetric (n := n) p) δ (y,s))=
      fun y=>(cotAngularScale s^2)⁻¹*normGradSqFun gA (fun z : PolarDir p=>δ (z,s)) y+
        (cotLineScale s^2)⁻¹*(deriv (fun t : ℝ=>δ (y,t)) s)^2 := by
    funext y
    exact DFLProductSlices.separated_gradient_energy_slices gA (cotProductMetric (n := n) p)
      cotAngularScale cotLineScale cotAngularScale_pos cotLineScale_pos (cotProductMetric_separated p) δ (y,s)
  unfold cotAngularDefect cotDeviationEnergy cotDeviationReducedEnergy cotDeviationPenalty cotDeviationHeightEnergy
  change _=_*(∫ y : PolarDir p,normGradSqFun (cotProductMetric (n := n) p) δ (y,s)
      ∂cotAngularVolume (n := n) p)-_
  rw [he,integral_add (hA.const_mul _) (hD.const_mul _),integral_const_mul,integral_const_mul]
  dsimp only [gA,δ]
  ring

theorem cotAngularDefect_integrable (hn : 1≤n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1),sphere (0 : E) 1;ℝ⟯) (r : ℝ) : Integrable (cotAngularDefect p u r) volume := by
  have he : cotAngularDefect p u r=fun s=>cotDeviationEnergy p u r s-cotDeviationReducedEnergy p u r s := by
    funext s; exact cotAngularDefect_eq_energy_sub_reduced p u r s
  rw [he]
  exact (cot_deviation_energy_integrable p u r).sub (cot_deviation_reduced_energy_integrable hn p u r)

/-- Actual equality of the complete transverse energy and the reduced
first-mode form forces angular sharp equality at every height. -/
theorem cot_deviation_energy_equality_angular (hn : 1≤n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1),sphere (0 : E) 1;ℝ⟯) (r : ℝ)
    (heq : (∫s,cotDeviationEnergy p u r s)=(∫s,cotDeviationReducedEnergy p u r s)) (s : ℝ) :
    (∫y : PolarDir p,normGradSqFun (roundMetric (E := (ℝ ∙ (p : E))ᗮ) (n := n))
      (fun z : PolarDir p=>cotDeviation p u (z,s)) y ∂cotAngularVolume (n := n) p)=
      (n : ℝ)*(∫y : PolarDir p,(cotDeviation p u (y,s))^2 ∂cotAngularVolume (n := n) p) := by
  have hDI := cotAngularDefect_integrable hn p u r
  have hzero : (∫s,cotAngularDefect p u r s)=0 := by
    calc
      _=∫s,cotDeviationEnergy p u r s-cotDeviationReducedEnergy p u r s := by
        apply integral_congr_ae; filter_upwards [] with t
        exact cotAngularDefect_eq_energy_sub_reduced p u r t
      _=0 := by rw [integral_sub (cot_deviation_energy_integrable p u r)
        (cot_deviation_reduced_energy_integrable hn p u r),heq,sub_self]
  have hAE : cotAngularDefect p u r=ᵐ[volume] (fun _=>0) :=
    (integral_eq_zero_iff_of_nonneg (cotAngularDefect_nonneg hn p u r) hDI).mp hzero
  have hpoint := congrFun (MeasureTheory.Measure.eq_of_ae_eq hAE
    (cotAngularDefect_continuous p u r) continuous_const) s
  have hpos : 0<(cotAngularScale s^n*cotLineScale s*Real.exp (r*(s*cotAngularScale s)))*(cotAngularScale s^2)⁻¹ :=
    mul_pos (mul_pos (mul_pos (pow_pos (cotAngularScale_pos s) n) (cotLineScale_pos s))
      (Real.exp_pos _)) (inv_pos.mpr (sq_pos_of_pos (cotAngularScale_pos s)))
  exact sub_eq_zero.mp ((mul_eq_zero.mp hpoint).resolve_left hpos.ne')

/-- The original angular part of a transverse equality state is a first
linear mode on every genuine angular sphere, including every circle fiber. -/
theorem cot_deviation_energy_equality_exists_linear (hn : 1≤n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1),sphere (0 : E) 1;ℝ⟯) (r : ℝ)
    (heq : (∫s,cotDeviationEnergy p u r s)=(∫s,cotDeviationReducedEnergy p u r s)) (s : ℝ) :
    ∃a : (ℝ ∙ (p : E))ᗮ,∀y : PolarDir p,cotDeviation p u (y,s)=⟪a,(y : (ℝ ∙ (p : E))ᗮ)⟫_ℝ := by
  let F : C^∞⟮𝓡 n,PolarDir p;ℝ⟯ :=
    ⟨fun y=>cotDeviation p u (y,s),(cotDeviation p u).contMDiff.comp (contMDiff_id.prodMk contMDiff_const)⟩
  exact DFLGenericRound.round_smooth_poincare_equality_exists_linear hn F
    (cotDeviation_mean_zero p u s) (cot_deviation_energy_equality_angular hn p u r heq s)

end DFLCotSphere
