import continuation.CotAngularEquality
import continuation.CotScalarPiconeEquality

/-! Equality in the actual transverse lower bound identifies the
manuscript's first separated angular mode. Genuine Fubini supplies scalar
equality on almost every fiber; continuity recovers every actual fiber. -/
noncomputable section
set_option maxHeartbeats 1200000
open Bundle Manifold MeasureTheory Metric Module Set Filter
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
namespace DFLCotSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+2)]
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p) := borel (PolarDir p)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p) := ⟨rfl⟩

/-- Equality at the actual transverse minimum saturates both the angular
sharp lower step and the true scalar Picone lower step. -/
theorem cot_transverse_equality_reduced (hn : 1≤n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1),sphere (0 : E) 1;ℝ⟯) (r : ℝ)
    (heq : (∫s,cotDeviationEnergy p u r s)=
      DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)*
        (∫s,cotTransverseMass p u r s)) :
    (∫s,cotDeviationEnergy p u r s)=(∫s,cotDeviationReducedEnergy p u r s) ∧
      (∫s,cotDeviationReducedEnergy p u r s)=
        DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)*
          (∫s,cotTransverseMass p u r s) := by
  have hlow := cot_transverse_first_minimum_lower hn p u r
  simp only [cot_transverse_reduced_eq] at hlow
  have hhigh := integral_mono (cot_deviation_reduced_energy_integrable hn p u r)
    (cot_deviation_energy_integrable p u r) (cot_deviation_reduced_slice_lower hn p u r)
  constructor <;> linarith

/-- Genuine scalar equality holds on almost every angular fiber; no scalar
integrability or scalar equality is supplied as an input. -/
theorem cot_transverse_reduced_equality_fibers (hn : 1≤n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1),sphere (0 : E) 1;ℝ⟯) (r : ℝ)
    (heq : (∫s,cotDeviationReducedEnergy p u r s)=
      DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)*
        (∫s,cotTransverseMass p u r s)) :
    ∀ᵐy∂cotAngularVolume (n := n) p,
      (∫s,cotTransverseScalarReduced p u r (y,s))=
        DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)*
          (∫s,cotTransverseScalarMass p u r (y,s)) := by
  let _ : SigmaFinite (cotAngularVolume (n := n) p) := riemannianVolumeMeasure_sigmaFinite _
  let lam := DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)
  have hM := cot_transverse_mass_integrable_product p u r
  have hE := cot_transverse_reduced_integrable_product hn p u r
  let D : PolarDir p → ℝ := fun y=>(∫s,cotTransverseScalarReduced p u r (y,s))-
    lam*(∫s,cotTransverseScalarMass p u r (y,s))
  have hDI : Integrable D (cotAngularVolume (n := n) p) :=
    hE.integral_prod_left.sub (hM.integral_prod_left.const_mul lam)
  have hNN : 0≤ᵐ[cotAngularVolume (n := n) p] D := by
    filter_upwards [hM.prod_right_ae,hE.prod_right_ae] with y hyM hyE
    exact sub_nonneg.mpr (cot_scalar_first_transverse_finite_lower n hn r
      (fun s=>cotDeviation p u (y,s)) (cot_deviation_real_slice_smooth p u y) hyM hyE)
  have hMFub := integral_integral_swap (f := fun y : PolarDir p=>fun s : ℝ=>
    cotTransverseScalarMass p u r (y,s)) hM
  have hEFub := integral_integral_swap (f := fun y : PolarDir p=>fun s : ℝ=>
    cotTransverseScalarReduced p u r (y,s)) hE
  have hzero : (∫y,D y ∂cotAngularVolume (n := n) p)=0 := by
    unfold D
    rw [integral_sub hE.integral_prod_left (hM.integral_prod_left.const_mul lam),integral_const_mul,
      hEFub,hMFub]
    change (∫s,cotTransverseReduced p u r s)-lam*(∫s,cotTransverseMass p u r s)=0
    simp only [cot_transverse_reduced_eq]
    rw [heq]
    exact sub_self _
  have hAE := (integral_eq_zero_iff_of_nonneg_ae hNN hDI).mp hzero
  filter_upwards [hAE] with y hy
  exact sub_eq_zero.mp hy

/-- Every genuine fiber has the same original ground shape; its multiplier
is its true equatorial value. This recovers all fibers from the a.e. Fubini
result using the actual open-positive angular volume. -/
theorem cot_transverse_equality_ground_ratio (hn : 1≤n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1),sphere (0 : E) 1;ℝ⟯) (r : ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (hpos : ∀t∈Icc (-1 : ℝ) 1,0<v t)
    (heig : DFL.Spectral.LatitudeEigenEquation (n+3) 1 ((n+1 : ℕ) : ℝ) r
      (DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)) v)
    (heq : (∫s,cotDeviationEnergy p u r s)=
      DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)*
        (∫s,cotTransverseMass p u r s)) :
    ∀y : PolarDir p,∀s : ℝ,cotDeviation p u (y,s)=
      (cotDeviation p u (y,0)/cotScalarGround v 0)*cotScalarGround v s := by
  let _ : SigmaFinite (cotAngularVolume (n := n) p) := riemannianVolumeMeasure_sigmaFinite _
  let _ : (cotAngularVolume (n := n) p).IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure _
  have hM := cot_transverse_mass_integrable_product p u r
  have hE := cot_transverse_reduced_integrable_product hn p u r
  have hAE := cot_transverse_reduced_equality_fibers hn p u r (cot_transverse_equality_reduced hn p u r heq).2
  have h0 : cotScalarGround v 0≠0 := (cotScalarGround_positive v hpos 0).ne'
  intro y s
  have hratioAE : (fun z : PolarDir p=>cotDeviation p u (z,s))=ᵐ[cotAngularVolume (n := n) p]
      fun z=>(cotDeviation p u (z,0)/cotScalarGround v 0)*cotScalarGround v s := by
    filter_upwards [hM.prod_right_ae,hE.prod_right_ae,hAE] with z hzM hzE hzEq
    obtain ⟨c,hc⟩ := cot_scalar_finite_equality_exists_ground_multiple n hn r _ v
      (fun t=>cotDeviation p u (z,t)) hv hpos heig (cot_deviation_real_slice_smooth p u z) hzM hzE hzEq
    rw [hc s,hc 0,mul_div_cancel_right₀ c h0]
  have hL : Continuous (fun z : PolarDir p=>cotDeviation p u (z,s)) :=
    (cotDeviation p u).contMDiff.continuous.comp (continuous_id.prodMk continuous_const)
  have hR : Continuous (fun z : PolarDir p=>(cotDeviation p u (z,0)/cotScalarGround v 0)*cotScalarGround v s) :=
    (((cotDeviation p u).contMDiff.continuous.comp
      (continuous_id.prodMk continuous_const)).div_const _).mul continuous_const
  exact congrFun (MeasureTheory.Measure.eq_of_ae_eq hratioAE hL hR) y

/-- Equality in the actual transverse lower bound is precisely the first
separated linear angular mode with the same original positive ground shape.
Neither the ground profile nor the separated-mode shape is assumed. -/
theorem cot_transverse_equality_exists_first_mode (hn : 1≤n) (p : sphere (0 : E) 1)
    (u : C^∞⟮𝓡 (n+1),sphere (0 : E) 1;ℝ⟯) (r : ℝ)
    (heq : (∫s,cotDeviationEnergy p u r s)=
      DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)*
        (∫s,cotTransverseMass p u r s)) :
    ∃(v : ℝ → ℝ) (a : (ℝ ∙ (p : E))ᗮ),ContDiff ℝ 2 v ∧
      (∀t∈Icc (-1 : ℝ) 1,0<v t) ∧
      DFL.Spectral.LatitudeEigenEquation (n+3) 1 ((n+1 : ℕ) : ℝ) r
        (DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)) v ∧
      ∀y : PolarDir p,∀s : ℝ,cotDeviation p u (y,s)=cotScalarGround v s*⟪a,(y : (ℝ ∙ (p : E))ᗮ)⟫_ℝ := by
  obtain ⟨v,hv,hpos,_hN,heig⟩ := DFL.Spectral.original_first_transverse_weighted_ground_exists (n+1) r
  obtain ⟨a,ha⟩ := cot_deviation_energy_equality_exists_linear hn p u r
    (cot_transverse_equality_reduced hn p u r heq).1 0
  refine ⟨v,(cotScalarGround v 0)⁻¹ • a,hv,hpos,heig,?_⟩
  intro y s
  rw [cot_transverse_equality_ground_ratio hn p u r v hv hpos heig heq y s,ha y,real_inner_smul_left]
  ring

end DFLCotSphere
