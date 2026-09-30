import continuation.CotScalarPicone
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Bounded

/-! The original two-pole finite-energy closure, in the natural complete cot
coordinate. Actual smooth cutoffs have derivative cost controlled by the
centrifugal term; no C2 regularity of the divided amplitude at the poles is
assumed. -/
noncomputable section
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter Metric Function
open scoped Topology ContDiff
namespace DFLCotSphere

def cotCutoffBase : ContDiffBump (0 : ℝ) := ⟨1,2,by norm_num,by norm_num⟩
def cotCutoff (R s : ℝ) : ℝ := cotCutoffBase (s/R)
def cotCutoffTest (R : ℝ) (phi : ℝ → ℝ) (s : ℝ) : ℝ := cotCutoff R s*phi s

theorem cotCutoff_smooth (R : ℝ) : ContDiff ℝ ∞ (cotCutoff R) :=
  cotCutoffBase.contDiff.comp (contDiff_id.div_const R)

theorem cotCutoffTest_smooth (R : ℝ) (phi : ℝ → ℝ) (hphi : ContDiff ℝ 2 phi) :
    ContDiff ℝ 2 (cotCutoffTest R phi) :=
  ((cotCutoff_smooth R).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).mul hphi

theorem cotCutoff_hasCompactSupport (R : ℝ) (hR : 0 < R) : HasCompactSupport (cotCutoff R) := by
  have h := cotCutoffBase.hasCompactSupport.comp_homeomorph
    (Homeomorph.mulRight₀ R⁻¹ (inv_ne_zero (ne_of_gt hR)))
  change HasCompactSupport (fun s : ℝ => cotCutoff R s)
  simpa only [Function.comp_def,Homeomorph.coe_mulRight₀,← div_eq_mul_inv,cotCutoff] using h

theorem cotCutoffTest_hasCompactSupport (R : ℝ) (hR : 0 < R) (phi : ℝ → ℝ) :
    HasCompactSupport (cotCutoffTest R phi) := (cotCutoff_hasCompactSupport R hR).mul_right

theorem cotCutoff_mem_Icc (R s : ℝ) : cotCutoff R s ∈ Icc (0 : ℝ) 1 :=
  ⟨cotCutoffBase.nonneg,cotCutoffBase.le_one⟩

theorem cotCutoff_one (R s : ℝ) (hR : 0 < R) (hs : |s| ≤ R) : cotCutoff R s = 1 := by
  apply cotCutoffBase.one_of_mem_closedBall
  change dist (s/R) 0 ≤ 1
  rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hR,div_le_one hR]
  exact hs

theorem cotCutoff_deriv (R s : ℝ) :
    deriv (cotCutoff R) s = deriv (cotCutoffBase : ℝ → ℝ) (s/R)/R := by
  have h := ((cotCutoffBase.contDiff (n := 1)).differentiable (by norm_num) (s/R)).hasDerivAt.comp s
    ((hasDerivAt_id s).div_const R)
  change deriv (fun x => cotCutoff R x) s = deriv (cotCutoffBase : ℝ → ℝ) (s/R)/R
  simpa only [cotCutoff,Function.comp_def,one_div,div_eq_mul_inv,id_eq,one_mul] using h.deriv

theorem cotCutoff_deriv_zero_inside (R s : ℝ) (hR : 0 < R) (hs : |s| < R) :
    deriv (cotCutoff R) s = 0 := by
  have hx : s/R ∈ ball (0 : ℝ) cotCutoffBase.rIn := by
    change dist (s/R) 0 < 1
    rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hR,div_lt_one hR]
    exact hs
  have he := cotCutoffBase.eventuallyEq_one_of_mem_ball hx
  have hz : deriv (cotCutoffBase : ℝ → ℝ) (s/R) = 0 := by
    rw [he.deriv_eq]
    exact deriv_const _ _
  rw [cotCutoff_deriv,hz,zero_div]

theorem cotCutoffBase_deriv_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ s : ℝ, |deriv (cotCutoffBase : ℝ → ℝ) s| ≤ C := by
  have hd : Continuous (deriv (cotCutoffBase : ℝ → ℝ)) :=
    (cotCutoffBase.contDiff (n := 1)).continuous_deriv (by norm_num)
  obtain ⟨C,hC⟩ := hd.bounded_above_of_compact_support cotCutoffBase.hasCompactSupport.deriv
  refine ⟨C,(norm_nonneg _).trans (hC 0),?_⟩
  intro s
  simpa only [Real.norm_eq_abs] using hC s

/-- A derivative can be nonzero only in the actual cutoff's outer support.
This fixes the natural pole scale in the centrifugal estimate. -/
theorem cotCutoff_deriv_nonzero_outer (R s : ℝ) (hR : 0 < R)
    (hd : deriv (cotCutoff R) s ≠ 0) : |s| ≤ 2*R := by
  have hdB : deriv (cotCutoffBase : ℝ → ℝ) (s/R) ≠ 0 := by
    intro hz
    apply hd
    rw [cotCutoff_deriv,hz,zero_div]
  have hs : s/R ∈ tsupport (cotCutoffBase : ℝ → ℝ) :=
    support_deriv_subset hdB
  rw [cotCutoffBase.tsupport_eq] at hs
  change dist (s/R) 0 ≤ 2 at hs
  rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hR] at hs
  exact (div_le_iff₀ hR).mp hs

/-- Genuine cutoff derivative energy has a uniform centrifugal domination.
The critical case is the growing cot annulus R<=|s|<=2R at either pole. -/
theorem cotCutoff_metric_cost_bound (C : ℝ)
    (hC : ∀ x : ℝ, |deriv (cotCutoffBase : ℝ → ℝ) x| ≤ C)
    (R s : ℝ) (hR : 1 ≤ R) :
    (cotLineScale s^2)⁻¹*(deriv (cotCutoff R) s)^2 ≤
      (5*C^2)*(cotAngularScale s^2)⁻¹ := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  by_cases hd : deriv (cotCutoff R) s = 0
  · rw [hd,zero_pow (by decide : 2 ≠ 0),mul_zero]
    positivity
  have hs := cotCutoff_deriv_nonzero_outer R s hRp hd
  have hs2 : s^2 ≤ 4*R^2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg s) (by positivity : 0 ≤ 2*R)).2 hs
    nlinarith [sq_abs s]
  have hR2 : 1 ≤ R^2 := by nlinarith
  have hds : (deriv (cotCutoff R) s)^2 ≤ C^2/R^2 := by
    rw [cotCutoff_deriv,div_pow]
    apply div_le_div_of_nonneg_right _ (sq_nonneg R)
    have hb := hC (s/R)
    have hc : 0 ≤ C := (abs_nonneg _).trans hb
    have hb2 := (sq_le_sq₀ (abs_nonneg _) hc).2 hb
    simpa only [sq_abs] using hb2
  have hf := cotAngularScale_pos s
  have hw := cotAngularScale_square_relation s
  have hfne := pow_ne_zero 2 (ne_of_gt hf)
  have hInv : (cotAngularScale s^2)⁻¹ = 1+s^2 := by
    apply mul_right_cancel₀ hfne
    rw [inv_mul_cancel₀ hfne]
    exact hw.symm
  rw [cotLineScale_eq_square,← inv_pow,hInv]
  apply (mul_le_mul_of_nonneg_left hds (sq_nonneg (1+s^2))).trans
  have hfrac : (1+s^2)/R^2 ≤ 5 := (div_le_iff₀ (pow_pos hRp 2)).2 (by nlinarith)
  calc
    (1+s^2)^2*(C^2/R^2) = (C^2*(1+s^2))*((1+s^2)/R^2) := by ring
    _ ≤ (C^2*(1+s^2))*5 :=
      mul_le_mul_of_nonneg_left hfrac (mul_nonneg (sq_nonneg C) (by positivity))
    _ = (5*C^2)*(1+s^2) := by ring

theorem cotCutoffTest_deriv (R : ℝ) (phi : ℝ → ℝ) (hphi : ContDiff ℝ 2 phi) (s : ℝ) :
    deriv (cotCutoffTest R phi) s =
      deriv (cotCutoff R) s*phi s+cotCutoff R s*deriv phi s := by
  have hc : ContDiff ℝ 2 (cotCutoff R) :=
    (cotCutoff_smooth R).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  exact (((hc.differentiable (by norm_num)) s).hasDerivAt.mul
    (((hphi.differentiable (by norm_num)) s).hasDerivAt)).deriv

theorem cotCutoffTest_mass_bound (n : ℕ) (r R : ℝ) (phi : ℝ → ℝ) (s : ℝ) :
    cotScalarMass n r (cotCutoffTest R phi) s ≤ cotScalarMass n r phi s := by
  have hk := cotCutoff_mem_Icc R s
  have hk2 : (cotCutoff R s)^2 ≤ 1 := by nlinarith [hk.1,hk.2]
  unfold cotScalarMass cotCutoffTest
  apply mul_le_mul_of_nonneg_left _ (cotScalarDensity_pos n r s).le
  rw [mul_pow]
  exact (mul_le_mul_of_nonneg_right hk2 (sq_nonneg _)).trans_eq (one_mul _)

/-- Uniform finite-energy domination of the actual cutoff reduced form.
The original centrifugal term is exactly what controls the pole cutoffs. -/
theorem cotCutoffTest_reduced_bound (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (C : ℝ)
    (hC : ∀ x : ℝ, |deriv (cotCutoffBase : ℝ → ℝ) x| ≤ C)
    (R : ℝ) (hR : 1 ≤ R) (phi : ℝ → ℝ) (hphi : ContDiff ℝ 2 phi) (s : ℝ) :
    cotScalarReducedForm n r (cotCutoffTest R phi) s ≤
      (3+10*C^2)*cotScalarReducedForm n r phi s := by
  let ρ := cotScalarDensity n r s
  let a := ρ*(cotLineScale s^2)⁻¹
  let b := ρ*cotScalarCentrifugal n s
  let k := cotCutoff R s
  let d := deriv (cotCutoff R) s
  let z := phi s
  let w := deriv phi s
  have hρ : 0 ≤ ρ := (cotScalarDensity_pos n r s).le
  have ha : 0 ≤ a := mul_nonneg hρ (inv_nonneg.mpr (sq_nonneg _))
  have hb : 0 ≤ b := mul_nonneg hρ (mul_nonneg (Nat.cast_nonneg n) (inv_nonneg.mpr (sq_nonneg _)))
  have hkI := cotCutoff_mem_Icc R s
  have hk : k^2 ≤ 1 := by dsimp [k]; nlinarith [hkI.1,hkI.2]
  have hA : 0 ≤ a*w^2 := mul_nonneg ha (sq_nonneg w)
  have hB : 0 ≤ b*z^2 := mul_nonneg hb (sq_nonneg z)
  have hV : (cotAngularScale s^2)⁻¹ ≤ cotScalarCentrifugal n s := by
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    simpa only [cotScalarCentrifugal,one_mul] using
      mul_le_mul_of_nonneg_right hnR (inv_nonneg.mpr (sq_nonneg (cotAngularScale s)))
  have hCost : (cotLineScale s^2)⁻¹*d^2 ≤ (5*C^2)*cotScalarCentrifugal n s :=
    (cotCutoff_metric_cost_bound C hC R s hR).trans
      (mul_le_mul_of_nonneg_left hV (by positivity))
  have hD : a*(d*z)^2 ≤ (5*C^2)*(b*z^2) := by
    calc
      _ = (ρ*z^2)*((cotLineScale s^2)⁻¹*d^2) := by dsimp [a]; ring
      _ ≤ (ρ*z^2)*((5*C^2)*cotScalarCentrifugal n s) :=
        mul_le_mul_of_nonneg_left hCost (mul_nonneg hρ (sq_nonneg z))
      _ = _ := by dsimp [b]; ring
  have hG : a*(k*w)^2 ≤ a*w^2 := by
    rw [mul_pow]
    have h := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hk (sq_nonneg w)) ha
    simpa only [one_mul] using h
  have hP : b*(k*z)^2 ≤ b*z^2 := by
    rw [mul_pow]
    have h := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hk (sq_nonneg z)) hb
    simpa only [one_mul] using h
  have hSquare : (d*z+k*w)^2 ≤ 2*(d*z)^2+2*(k*w)^2 := by
    nlinarith [sq_nonneg (d*z-k*w)]
  have hGrad : a*(d*z+k*w)^2 ≤ 2*(a*w^2)+(10*C^2)*(b*z^2) := by
    have h := mul_le_mul_of_nonneg_left hSquare ha
    nlinarith
  have hTotal : a*(d*z+k*w)^2+b*(k*z)^2 ≤ (3+10*C^2)*(a*w^2+b*z^2) := by
    have hCA : 0 ≤ C^2*(a*w^2) := mul_nonneg (sq_nonneg C) hA
    nlinarith
  rw [cotScalarReducedForm,cotScalarReducedForm,cotCutoffTest_deriv R phi hphi s]
  change ρ*((cotLineScale s^2)⁻¹*(d*z+k*w)^2+cotScalarCentrifugal n s*(k*z)^2) ≤
    (3+10*C^2)*(ρ*((cotLineScale s^2)⁻¹*w^2+cotScalarCentrifugal n s*z^2))
  simpa only [a,b,mul_add,mul_assoc] using hTotal

private theorem cotScalarMass_nonneg (n : ℕ) (r : ℝ) (phi : ℝ → ℝ) (s : ℝ) :
    0 ≤ cotScalarMass n r phi s :=
  mul_nonneg (cotScalarDensity_pos n r s).le (sq_nonneg _)

private theorem cotScalarReducedForm_nonneg (n : ℕ) (r : ℝ) (phi : ℝ → ℝ) (s : ℝ) :
    0 ≤ cotScalarReducedForm n r phi s := by
  unfold cotScalarReducedForm cotScalarCentrifugal
  exact mul_nonneg (cotScalarDensity_pos n r s).le
    (add_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (inv_nonneg.mpr (sq_nonneg _))) (sq_nonneg _)))

private theorem cotScalarReducedForm_continuous (n : ℕ) (r : ℝ) (phi : ℝ → ℝ)
    (hphi : ContDiff ℝ 2 phi) : Continuous (cotScalarReducedForm n r phi) :=
  (cotScalarDensity_continuous n r).mul
    ((((cotLineScale_smooth.continuous.pow 2).inv₀
      (fun s => pow_ne_zero 2 (ne_of_gt (cotLineScale_pos s)))).mul
      ((hphi.deriv' : ContDiff ℝ 1 (deriv phi)).continuous.pow 2)).add
      ((cotScalarCentrifugal_continuous n).mul (hphi.continuous.pow 2)))

/-- On each fixed true cot point, the cutoff and its derivative eventually
leave the original test unchanged. -/
theorem cotCutoffTest_eventually_eq (phi : ℝ → ℝ) (hphi : ContDiff ℝ 2 phi) (s : ℝ) :
    ∀ᶠ R : ℝ in atTop, cotCutoffTest R phi s = phi s ∧
      deriv (cotCutoffTest R phi) s = deriv phi s := by
  filter_upwards [eventually_gt_atTop (|s|+1)] with R hR
  have hRp : 0 < R := by linarith [abs_nonneg s]
  have hs : |s| < R := by linarith
  have hOne := cotCutoff_one R s hRp hs.le
  have hZero := cotCutoff_deriv_zero_inside R s hRp hs
  constructor
  · unfold cotCutoffTest
    rw [hOne,one_mul]
  · rw [cotCutoffTest_deriv R phi hphi s,hZero,hOne,zero_mul,one_mul,zero_add]

/-- Actual finite physical mass converges under the true pole cutoffs. -/
theorem cot_scalar_mass_cutoff_tendsto (n : ℕ) (r : ℝ) (phi : ℝ → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hMass : Integrable (cotScalarMass n r phi) volume) :
    Tendsto (fun R : ℝ => ∫ s : ℝ, cotScalarMass n r (cotCutoffTest R phi) s)
      atTop (𝓝 (∫ s : ℝ, cotScalarMass n r phi s)) := by
  refine tendsto_integral_filter_of_dominated_convergence (cotScalarMass n r phi) ?_ ?_ hMass ?_
  · filter_upwards [] with R
    have hc : Continuous (cotScalarMass n r (cotCutoffTest R phi)) :=
      (cotScalarDensity_continuous n r).mul ((cotCutoffTest_smooth R phi hphi).continuous.pow 2)
    exact hc.aestronglyMeasurable
  · filter_upwards [] with R
    filter_upwards [] with s
    rw [Real.norm_eq_abs,abs_of_nonneg (cotScalarMass_nonneg n r (cotCutoffTest R phi) s)]
    exact cotCutoffTest_mass_bound n r R phi s
  · filter_upwards [] with s
    have heq : (fun R : ℝ => cotScalarMass n r (cotCutoffTest R phi) s) =ᶠ[atTop]
        fun _ => cotScalarMass n r phi s := by
      filter_upwards [cotCutoffTest_eventually_eq phi hphi s] with R hR
      unfold cotScalarMass
      rw [hR.1]
    exact tendsto_const_nhds.congr' heq.symm

/-- The whole original reduced energy converges under actual smooth pole
cutoffs. Domination comes from the actual finite centrifugal and derivative
energy, with no endpoint amplitude regularity requirement. -/
theorem cot_scalar_reduced_cutoff_tendsto (n : ℕ) (hn : 1 ≤ n) (r C : ℝ)
    (hC : ∀ x : ℝ, |deriv (cotCutoffBase : ℝ → ℝ) x| ≤ C)
    (phi : ℝ → ℝ) (hphi : ContDiff ℝ 2 phi)
    (hEnergy : Integrable (cotScalarReducedForm n r phi) volume) :
    Tendsto (fun R : ℝ => ∫ s : ℝ, cotScalarReducedForm n r (cotCutoffTest R phi) s)
      atTop (𝓝 (∫ s : ℝ, cotScalarReducedForm n r phi s)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun s => (3+10*C^2)*cotScalarReducedForm n r phi s) ?_ ?_ (hEnergy.const_mul _) ?_
  · filter_upwards [] with R
    exact (cotScalarReducedForm_continuous n r (cotCutoffTest R phi)
      (cotCutoffTest_smooth R phi hphi)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    filter_upwards [] with s
    rw [Real.norm_eq_abs,abs_of_nonneg (cotScalarReducedForm_nonneg n r (cotCutoffTest R phi) s)]
    exact cotCutoffTest_reduced_bound n hn r C hC R hR phi hphi s
  · filter_upwards [] with s
    have heq : (fun R : ℝ => cotScalarReducedForm n r (cotCutoffTest R phi) s) =ᶠ[atTop]
        fun _ => cotScalarReducedForm n r phi s := by
      filter_upwards [cotCutoffTest_eventually_eq phi hphi s] with R hR
      unfold cotScalarReducedForm
      rw [hR.1,hR.2]
    exact tendsto_const_nhds.congr' heq.symm

/-- The original actual transverse minimum bounds every genuine C2 cot
state with finite physical mass and finite complete reduced energy. The
compact core, pole cutoffs and limiting step are all proved. -/
theorem cot_scalar_first_transverse_finite_lower (n : ℕ) (hn : 1 ≤ n) (r : ℝ)
    (phi : ℝ → ℝ) (hphi : ContDiff ℝ 2 phi)
    (hMass : Integrable (cotScalarMass n r phi) volume)
    (hEnergy : Integrable (cotScalarReducedForm n r phi) volume) :
    DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)*
      (∫ s : ℝ, cotScalarMass n r phi s) ≤ ∫ s : ℝ, cotScalarReducedForm n r phi s := by
  obtain ⟨C,_,hC⟩ := cotCutoffBase_deriv_bound
  have hMLim := cot_scalar_mass_cutoff_tendsto n r phi hphi hMass
  have hELim := cot_scalar_reduced_cutoff_tendsto n hn r C hC phi hphi hEnergy
  have hIneq : ∀ᶠ R : ℝ in atTop,
      DFLSphere.roundTiltMinimum (n+1) ((n+1 : ℕ) : ℝ) r (((n+1 : ℕ) : ℝ)/2)*
        (∫ s : ℝ, cotScalarMass n r (cotCutoffTest R phi) s) ≤
          ∫ s : ℝ, cotScalarReducedForm n r (cotCutoffTest R phi) s := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact cot_scalar_first_transverse_compact_lower n r (cotCutoffTest R phi)
      (cotCutoffTest_smooth R phi hphi)
      (cotCutoffTest_hasCompactSupport R (lt_of_lt_of_le zero_lt_one hR) phi)
  exact le_of_tendsto_of_tendsto (tendsto_const_nhds.mul hMLim) hELim hIneq

end DFLCotSphere
