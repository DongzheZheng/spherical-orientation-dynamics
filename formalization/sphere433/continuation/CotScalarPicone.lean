import continuation.CotAngularDeviationCoercivity
import continuation.OriginalWeightedGround
import continuation.LatMeasureIdentity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support

/-! The manuscript's scalar positive-ground Picone argument on the entire
cot line. Compact support removes boundary fluxes without imposing false
smooth extension conditions at the two physical poles. -/
noncomputable section
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace DFLCotSphere

/-- The same elementary ground transform used in the original latitude
Picone proof, on the complete cot line with a true compact test. -/
theorem compact_ground_picone (p rho V h phi : ℝ → ℝ) (lam : ℝ)
    (hp : Continuous p) (hrho : Continuous rho) (hV : Continuous V)
    (hh : ContDiff ℝ 2 h) (hphi : ContDiff ℝ 2 phi)
    (hpos : ∀ s, 0 < h s) (hcompact : HasCompactSupport phi)
    (hflux : ∀ s, HasDerivAt (fun x => p x*deriv h x)
      (rho s*(V s-lam)*h s) s) :
    (∫ s : ℝ, p s*(deriv phi s)^2+rho s*(V s-lam)*(phi s)^2) =
      ∫ s : ℝ, p s*(deriv phi s-phi s*(deriv h s/h s))^2 := by
  have hd := hh.differentiable (by norm_num)
  have hpd := hphi.differentiable (by norm_num)
  have hdc : Continuous (deriv h) := (hh.deriv' : ContDiff ℝ 1 (deriv h)).continuous
  have hpdc : Continuous (deriv phi) := (hphi.deriv' : ContDiff ℝ 1 (deriv phi)).continuous
  let F : ℝ → ℝ := fun s => (phi s)^2*((p s*deriv h s)/h s)
  let E : ℝ → ℝ := fun s => p s*(deriv phi s)^2+rho s*(V s-lam)*(phi s)^2
  let A : ℝ → ℝ := fun s => p s*(deriv phi s-phi s*(deriv h s/h s))^2
  have hF : Continuous F := (hphi.continuous.pow 2).mul
    ((hp.mul hdc).div hh.continuous (fun s => ne_of_gt (hpos s)))
  have hE : Continuous E := (hp.mul (hpdc.pow 2)).add
    ((hrho.mul (hV.sub continuous_const)).mul (hphi.continuous.pow 2))
  have hA : Continuous A := hp.mul
    ((hpdc.sub (hphi.continuous.mul (hdc.div hh.continuous (fun s => ne_of_gt (hpos s))))).pow 2)
  have hsphi : HasCompactSupport (fun s => (phi s)^2) := hcompact.comp_left (g := fun x : ℝ => x^2) (by norm_num)
  have hsdphi : HasCompactSupport (fun s => (deriv phi s)^2) := hcompact.deriv.comp_left (g := fun x : ℝ => x^2) (by norm_num)
  have hsF : HasCompactSupport F := hsphi.mul_right
  have hsFirst : HasCompactSupport (fun s => p s*(deriv phi s)^2) := hsdphi.mul_left
  have hsSecond : HasCompactSupport (fun s => rho s*(V s-lam)*(phi s)^2) := hsphi.mul_left
  have hsE : HasCompactSupport E := hsFirst.add hsSecond
  have hsDiff : HasCompactSupport (fun s => deriv phi s-phi s*(deriv h s/h s)) :=
    hcompact.deriv.sub (hcompact.mul_right (f' := fun s => deriv h s/h s))
  have hsSq : HasCompactSupport (fun s => (deriv phi s-phi s*(deriv h s/h s))^2) :=
    hsDiff.comp_left (g := fun x : ℝ => x^2) (by norm_num)
  have hsA : HasCompactSupport A := hsSq.mul_left
  have hFI : Integrable F := hF.integrable_of_hasCompactSupport hsF
  have hEI : Integrable E := hE.integrable_of_hasCompactSupport hsE
  have hAI : Integrable A := hA.integrable_of_hasCompactSupport hsA
  have hFD : ∀ s, HasDerivAt F (E s-A s) s := by
    intro s
    convert! ((hpd s).hasDerivAt.pow 2).mul
      ((hflux s).div (hd s).hasDerivAt (ne_of_gt (hpos s))) using 1
    dsimp [F,E,A]
    field_simp [ne_of_gt (hpos s)]
    ring
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hFD (hEI.sub hAI) hFI
  rw [integral_sub hEI hAI] at hz
  exact sub_eq_zero.mp hz

/-- Original compact-test Rayleigh inequality obtained from the actual
positive ground flux equation, not from an assumed variational lower bound. -/
theorem compact_ground_rayleigh (p rho V h phi : ℝ → ℝ) (lam : ℝ)
    (hp : Continuous p) (hrho : Continuous rho) (hV : Continuous V)
    (hh : ContDiff ℝ 2 h) (hphi : ContDiff ℝ 2 phi)
    (hpos : ∀ s, 0 < h s) (hcompact : HasCompactSupport phi)
    (hpnonneg : ∀ s, 0 ≤ p s)
    (hflux : ∀ s, HasDerivAt (fun x => p x*deriv h x)
      (rho s*(V s-lam)*h s) s) :
    0 ≤ ∫ s : ℝ, p s*(deriv phi s)^2+rho s*(V s-lam)*(phi s)^2 := by
  rw [compact_ground_picone p rho V h phi lam hp hrho hV hh hphi hpos hcompact hflux]
  exact integral_nonneg (fun s => mul_nonneg (hpnonneg s) (sq_nonneg _))

/-- Genuine angular scale derivative on the entire cot line. -/
theorem cotAngularScale_hasDerivAt (s : ℝ) :
    HasDerivAt cotAngularScale (-s*cotAngularScale s^3) s := by
  have h := (Real.hasDerivAt_sin (cotAngle s)).comp s (cotAngle_hasDerivAt s)
  have he : Real.sin ∘ cotAngle = cotAngularScale := funext cotAngle_sin
  rw [he] at h
  convert! h using 1
  rw [cotAngle_cos,cotLineScale_eq_square]
  ring

/-- The original physical scalar density on the entire cot line. -/
def cotScalarDensity (n : ℕ) (r s : ℝ) : ℝ :=
  cotAngularScale s^n*cotLineScale s*Real.exp (r*cotHeight s)

def cotScalarFluxWeight (n : ℕ) (r s : ℝ) : ℝ :=
  cotScalarDensity n r s*(cotLineScale s^2)⁻¹

def cotScalarCentrifugal (n : ℕ) (s : ℝ) : ℝ :=
  (n : ℝ)*(cotAngularScale s^2)⁻¹

def cotScalarGround (v : ℝ → ℝ) (s : ℝ) : ℝ :=
  cotAngularScale s*v (cotHeight s)

theorem cotScalarGround_smooth (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) :
    ContDiff ℝ 2 (cotScalarGround v) := by
  have hf : ContDiff ℝ 2 cotAngularScale := cotAngularScale_smooth.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have ht : ContDiff ℝ 2 cotHeight := cotHeight_smooth.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  exact hf.mul (hv.comp ht)

theorem cotScalarGround_positive (v : ℝ → ℝ)
    (hpos : ∀ t ∈ Icc (-1 : ℝ) 1, 0 < v t) (s : ℝ) :
    0 < cotScalarGround v s := by
  exact mul_pos (cotAngularScale_pos s)
    (hpos (cotHeight s) ⟨(cotHeight_mem s).1.le,(cotHeight_mem s).2.le⟩)

theorem cotScalarGround_deriv (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (s : ℝ) :
    deriv (cotScalarGround v) s =
      -s*cotAngularScale s^3*v (cotHeight s)+cotAngularScale s^4*deriv v (cotHeight s) := by
  have h := (cotAngularScale_hasDerivAt s).mul
    (((hv.differentiable (by norm_num)) (cotHeight s)).hasDerivAt.comp s (cotHeight_hasDerivAt s))
  convert! h.deriv using 1
  simp only [Function.comp_apply]
  ring

theorem cotAngularScale_square_relation (s : ℝ) :
    (1+s^2)*cotAngularScale s^2 = 1 := by
  have h := cotHeight_w s
  dsimp [cotHeight] at h
  nlinarith

/-- Exact original cot flux of the same first-transverse weighted profile. -/
theorem cotScalarGround_flux_explicit (n : ℕ) (r : ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (s : ℝ) :
    cotScalarFluxWeight n r s*deriv (cotScalarGround v) s =
      (cotAngularScale s^(n+2)*Real.exp (r*cotHeight s))*deriv v (cotHeight s)-
        (s*cotAngularScale s^(n+1)*Real.exp (r*cotHeight s))*v (cotHeight s) := by
  unfold cotScalarFluxWeight cotScalarDensity
  rw [cotScalarGround_deriv v hv s,cotLineScale_eq_square]
  simp only [pow_add,pow_two,pow_one]
  field_simp [ne_of_gt (cotAngularScale_pos s)]
  ring

/-- The manuscript's original weighted latitude eigen-equation becomes the
true centrifugal Schrödinger flux equation on the entire cot line. -/
theorem cotScalarGround_flux_hasDerivAt (n : ℕ) (r lam : ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v)
    (heig : DFL.Spectral.LatitudeEigenEquation (n+3) 1 ((n+1 : ℕ) : ℝ) r lam v)
    (s : ℝ) :
    HasDerivAt (fun x => cotScalarFluxWeight n r x*deriv (cotScalarGround v) x)
      (cotScalarDensity n r s*(cotScalarCentrifugal n s-lam)*cotScalarGround v s) s := by
  have hf := cotAngularScale_hasDerivAt s
  have ht := cotHeight_hasDerivAt s
  have he : HasDerivAt (fun x : ℝ => Real.exp (r*cotHeight x))
      (Real.exp (r*cotHeight s)*(r*cotAngularScale s^3)) s :=
    by simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (r*cotHeight s)).comp s (ht.const_mul r)
  have hvd := hv.differentiable (by norm_num)
  have hvdd := (hv.deriv' : ContDiff ℝ 1 (deriv v)).differentiable (by norm_num)
  have hvc := (hvd (cotHeight s)).hasDerivAt.comp s ht
  have hdvc := (hvdd (cotHeight s)).hasDerivAt.comp s ht
  have hA := (hf.pow (n+2)).mul he
  have hB := ((hasDerivAt_id s).mul (hf.pow (n+1))).mul he
  have hZ := (hA.mul hdvc).sub (hB.mul hvc)
  have hfun : (fun x : ℝ => cotScalarFluxWeight n r x*deriv (cotScalarGround v) x) =
      fun x : ℝ => (cotAngularScale x^(n+2)*Real.exp (r*cotHeight x))*deriv v (cotHeight x)-
        (x*cotAngularScale x^(n+1)*Real.exp (r*cotHeight x))*v (cotHeight x) :=
    funext (cotScalarGround_flux_explicit n r v hv)
  change HasDerivAt (fun x : ℝ =>
    (cotAngularScale x^(n+2)*Real.exp (r*cotHeight x))*deriv v (cotHeight x)-
      (x*cotAngularScale x^(n+1)*Real.exp (r*cotHeight x))*v (cotHeight x)) _ s at hZ
  rw [← hfun] at hZ
  have hODE := heig (cotHeight s) (cotHeight_mem s)
  rw [cotHeight_w] at hODE
  dsimp [cotHeight] at hODE
  push_cast at hODE
  have hw := cotAngularScale_square_relation s
  convert! hZ using 1
  dsimp [cotScalarDensity,cotScalarCentrifugal,cotScalarGround]
  rw [cotLineScale_eq_square]
  simp only [Nat.cast_add,Nat.cast_ofNat,pow_add,pow_two,pow_one]
  field_simp [ne_of_gt (cotAngularScale_pos s)]
  dsimp [cotHeight]
  linear_combination (cotAngularScale s^2)*hODE -
    (((n : ℝ)+1)*v (s*cotAngularScale s))*hw

theorem cotScalarDensity_continuous (n : ℕ) (r : ℝ) : Continuous (cotScalarDensity n r) :=
  ((cotAngularScale_smooth.continuous.pow n).mul cotLineScale_smooth.continuous).mul
    (Real.continuous_exp.comp (continuous_const.mul cotHeight_smooth.continuous))

theorem cotScalarFluxWeight_continuous (n : ℕ) (r : ℝ) : Continuous (cotScalarFluxWeight n r) :=
  (cotScalarDensity_continuous n r).mul
    ((cotLineScale_smooth.continuous.pow 2).inv₀
      (fun s => pow_ne_zero 2 (ne_of_gt (cotLineScale_pos s))))

theorem cotScalarCentrifugal_continuous (n : ℕ) : Continuous (cotScalarCentrifugal n) :=
  continuous_const.mul ((cotAngularScale_smooth.continuous.pow 2).inv₀
    (fun s => pow_ne_zero 2 (ne_of_gt (cotAngularScale_pos s))))

theorem cotScalarDensity_pos (n : ℕ) (r s : ℝ) : 0 < cotScalarDensity n r s :=
  mul_pos (mul_pos (pow_pos (cotAngularScale_pos s) n) (cotLineScale_pos s)) (Real.exp_pos _)

/-- The same actual positive original profile supplies the cot Picone square
for every true compact scalar test. -/
theorem cot_scalar_profile_compact_picone (n : ℕ) (r lam : ℝ) (v phi : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (hpos : ∀ t ∈ Icc (-1 : ℝ) 1, 0 < v t)
    (heig : DFL.Spectral.LatitudeEigenEquation (n+3) 1 ((n+1 : ℕ) : ℝ) r lam v)
    (hphi : ContDiff ℝ 2 phi) (hcompact : HasCompactSupport phi) :
    (∫ s : ℝ, cotScalarFluxWeight n r s*(deriv phi s)^2+
      cotScalarDensity n r s*(cotScalarCentrifugal n s-lam)*(phi s)^2) =
      ∫ s : ℝ, cotScalarFluxWeight n r s*
        (deriv phi s-phi s*(deriv (cotScalarGround v) s/cotScalarGround v s))^2 :=
  compact_ground_picone _ _ _ _ _ lam (cotScalarFluxWeight_continuous n r)
    (cotScalarDensity_continuous n r) (cotScalarCentrifugal_continuous n)
    (cotScalarGround_smooth v hv) hphi (cotScalarGround_positive v hpos) hcompact
    (cotScalarGround_flux_hasDerivAt n r lam v hv heig)

/-- The actual physical transverse scalar reduced form. -/
def cotScalarReducedForm (n : ℕ) (r : ℝ) (phi : ℝ → ℝ) (s : ℝ) : ℝ :=
  cotScalarDensity n r s*((cotLineScale s^2)⁻¹*(deriv phi s)^2+
    cotScalarCentrifugal n s*(phi s)^2)

def cotScalarMass (n : ℕ) (r : ℝ) (phi : ℝ → ℝ) (s : ℝ) : ℝ :=
  cotScalarDensity n r s*(phi s)^2

/-- Genuine original transverse minimum bounds every true compact cot test.
The original positive ground existence and its ODE are both discharged. -/
theorem cot_scalar_first_transverse_compact_lower (n : ℕ) (r : ℝ) (phi : ℝ → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hcompact : HasCompactSupport phi) :
    DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)*
      (∫ s : ℝ, cotScalarMass n r phi s) ≤ ∫ s : ℝ, cotScalarReducedForm n r phi s := by
  obtain ⟨v,hv,hpos,_,heig⟩ :=
    DFL.Spectral.original_first_transverse_weighted_ground_exists (n+1) r
  have h := compact_ground_rayleigh (cotScalarFluxWeight n r) (cotScalarDensity n r)
    (cotScalarCentrifugal n) (cotScalarGround v) phi
    (DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2))
    (cotScalarFluxWeight_continuous n r) (cotScalarDensity_continuous n r)
    (cotScalarCentrifugal_continuous n) (cotScalarGround_smooth v hv) hphi
    (cotScalarGround_positive v hpos) hcompact
    (fun s => mul_nonneg (cotScalarDensity_pos n r s).le
      (inv_nonneg.mpr (sq_nonneg _)))
    (cotScalarGround_flux_hasDerivAt n r _ v hv (by simpa only [Nat.add_assoc] using heig))
  have hds : Continuous (deriv phi) := (hphi.deriv' : ContDiff ℝ 1 (deriv phi)).continuous
  have hmC : Continuous (cotScalarMass n r phi) :=
    (cotScalarDensity_continuous n r).mul (hphi.continuous.pow 2)
  have heC : Continuous (cotScalarReducedForm n r phi) :=
    (cotScalarDensity_continuous n r).mul
      (((cotLineScale_smooth.continuous.pow 2).inv₀
        (fun s => pow_ne_zero 2 (ne_of_gt (cotLineScale_pos s)))).mul (hds.pow 2) |>.add
        ((cotScalarCentrifugal_continuous n).mul (hphi.continuous.pow 2)))
  have hsphi : HasCompactSupport (fun s => (phi s)^2) :=
    hcompact.comp_left (g := fun x : ℝ => x^2) (by norm_num)
  have hsdphi : HasCompactSupport (fun s => (deriv phi s)^2) :=
    hcompact.deriv.comp_left (g := fun x : ℝ => x^2) (by norm_num)
  have hmS : HasCompactSupport (cotScalarMass n r phi) := hsphi.mul_left
  have hsFirst : HasCompactSupport (fun s => (cotLineScale s^2)⁻¹*(deriv phi s)^2) := hsdphi.mul_left
  have hsSecond : HasCompactSupport (fun s => cotScalarCentrifugal n s*(phi s)^2) := hsphi.mul_left
  have heS : HasCompactSupport (cotScalarReducedForm n r phi) := (hsFirst.add hsSecond).mul_left
  have hmI : Integrable (cotScalarMass n r phi) volume := hmC.integrable_of_hasCompactSupport hmS
  have heI : Integrable (cotScalarReducedForm n r phi) volume := heC.integrable_of_hasCompactSupport heS
  have hid : (fun s : ℝ => cotScalarFluxWeight n r s*(deriv phi s)^2+
      cotScalarDensity n r s*(cotScalarCentrifugal n s-
        DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2))*(phi s)^2) =
      fun s => cotScalarReducedForm n r phi s-
        DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)*
          cotScalarMass n r phi s := by
    funext s
    dsimp [cotScalarFluxWeight,cotScalarReducedForm,cotScalarMass]
    ring
  rw [hid,integral_sub heI (hmI.const_mul _),integral_const_mul] at h
  exact sub_nonneg.mp h

end DFLCotSphere
