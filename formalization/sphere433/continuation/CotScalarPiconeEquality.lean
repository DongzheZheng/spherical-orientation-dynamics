import continuation.CotScalarCutoff
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! The original finite-energy Picone equality case. Compact tests,
proved pole cutoffs and Fatou yield zero ground-transform derivative;
the original scalar state is a constant multiple of its positive ground. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal
namespace DFLCotSphere

def cotScalarPiconeSquare (n : ℕ) (r : ℝ) (v phi : ℝ → ℝ) (s : ℝ) : ℝ :=
  cotScalarFluxWeight n r s*(deriv phi s-phi s*(deriv (cotScalarGround v) s/cotScalarGround v s))^2

theorem cotScalarPiconeSquare_continuous (n : ℕ) (r : ℝ) (v phi : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (hphi : ContDiff ℝ 2 phi)
    (hpos : ∀t∈Icc (-1 : ℝ) 1,0<v t) : Continuous (cotScalarPiconeSquare n r v phi) := by
  have hh := cotScalarGround_smooth v hv
  exact (cotScalarFluxWeight_continuous n r).mul
    (((hphi.deriv' : ContDiff ℝ 1 (deriv phi)).continuous.sub
      (hphi.continuous.mul (((hh.deriv' : ContDiff ℝ 1 (deriv (cotScalarGround v))).continuous).div
        hh.continuous (fun s=>(cotScalarGround_positive v hpos s).ne')))).pow 2)

theorem cotScalarPiconeSquare_nonneg (n : ℕ) (r : ℝ) (v phi : ℝ → ℝ) (s : ℝ) :
    0≤cotScalarPiconeSquare n r v phi s :=
  mul_nonneg (mul_nonneg (cotScalarDensity_pos n r s).le (inv_nonneg.mpr (sq_nonneg _))) (sq_nonneg _)

theorem cotScalarPiconeSquare_compact_integrable (n : ℕ) (r : ℝ) (v phi : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (hphi : ContDiff ℝ 2 phi)
    (hpos : ∀t∈Icc (-1 : ℝ) 1,0<v t) (hcompact : HasCompactSupport phi) :
    Integrable (cotScalarPiconeSquare n r v phi) volume := by
  have hs : HasCompactSupport (fun s=>deriv phi s-phi s*(deriv (cotScalarGround v) s/cotScalarGround v s)) :=
    hcompact.deriv.sub (hcompact.mul_right (f' := fun s=>deriv (cotScalarGround v) s/cotScalarGround v s))
  exact (cotScalarPiconeSquare_continuous n r v phi hv hphi hpos).integrable_of_hasCompactSupport
    ((hs.comp_left (g := fun z : ℝ=>z^2) (by norm_num)).mul_left)

private theorem reduced_compact_integrable (n : ℕ) (r : ℝ) (phi : ℝ → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hcompact : HasCompactSupport phi) :
    Integrable (cotScalarReducedForm n r phi) volume := by
  have hC : Continuous (cotScalarReducedForm n r phi) :=
    (cotScalarDensity_continuous n r).mul
      ((((cotLineScale_smooth.continuous.pow 2).inv₀
        (fun s=>pow_ne_zero 2 (cotLineScale_pos s).ne')).mul
        ((hphi.deriv' : ContDiff ℝ 1 (deriv phi)).continuous.pow 2)).add
        ((cotScalarCentrifugal_continuous n).mul (hphi.continuous.pow 2)))
  have hsD : HasCompactSupport (fun s : ℝ=>(deriv phi s)^2) :=
    hcompact.deriv.comp_left (g := fun z : ℝ=>z^2) (by norm_num)
  have hsM : HasCompactSupport (fun s : ℝ=>(phi s)^2) :=
    hcompact.comp_left (g := fun z : ℝ=>z^2) (by norm_num)
  have hs1 : HasCompactSupport (fun s : ℝ=>(cotLineScale s^2)⁻¹*(deriv phi s)^2) := hsD.mul_left
  have hs2 : HasCompactSupport (fun s : ℝ=>cotScalarCentrifugal n s*(phi s)^2) := hsM.mul_left
  have hsInner : HasCompactSupport (fun s : ℝ=>(cotLineScale s^2)⁻¹*(deriv phi s)^2+
      cotScalarCentrifugal n s*(phi s)^2) := hs1.add hs2
  exact hC.integrable_of_hasCompactSupport hsInner.mul_left

private theorem mass_compact_integrable (n : ℕ) (r : ℝ) (phi : ℝ → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hcompact : HasCompactSupport phi) :
    Integrable (cotScalarMass n r phi) volume := by
  have hC : Continuous (cotScalarMass n r phi) :=
    (cotScalarDensity_continuous n r).mul (hphi.continuous.pow 2)
  have hsM : HasCompactSupport (fun s : ℝ=>(phi s)^2) :=
    hcompact.comp_left (g := fun z : ℝ=>z^2) (by norm_num)
  exact hC.integrable_of_hasCompactSupport hsM.mul_left

theorem cot_scalar_compact_picone_energy_identity (n : ℕ) (r lam : ℝ) (v phi : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (hpos : ∀t∈Icc (-1 : ℝ) 1,0<v t)
    (heig : DFL.Spectral.LatitudeEigenEquation (n+3) 1 ((n+1 : ℕ) : ℝ) r lam v)
    (hphi : ContDiff ℝ 2 phi) (hcompact : HasCompactSupport phi) :
    (∫s,cotScalarPiconeSquare n r v phi s)=
      (∫s,cotScalarReducedForm n r phi s)-lam*(∫s,cotScalarMass n r phi s) := by
  have hP := cot_scalar_profile_compact_picone n r lam v phi hv hpos heig hphi hcompact
  have he : (fun s=>cotScalarFluxWeight n r s*(deriv phi s)^2+
      cotScalarDensity n r s*(cotScalarCentrifugal n s-lam)*(phi s)^2)=
      fun s=>cotScalarReducedForm n r phi s-lam*cotScalarMass n r phi s := by
    funext s
    unfold cotScalarFluxWeight cotScalarReducedForm cotScalarMass
    ring
  rw [he,integral_sub (reduced_compact_integrable n r phi hphi hcompact)
    ((mass_compact_integrable n r phi hphi hcompact).const_mul lam),integral_const_mul] at hP
  exact hP.symm

/-- Equality of the genuine finite cot form forces every Picone square
to vanish. Fatou uses only the already proved true cutoff convergence. -/
theorem cot_scalar_finite_equality_picone_zero (n : ℕ) (hn : 1≤n) (r lam : ℝ) (v phi : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (hpos : ∀t∈Icc (-1 : ℝ) 1,0<v t)
    (heig : DFL.Spectral.LatitudeEigenEquation (n+3) 1 ((n+1 : ℕ) : ℝ) r lam v)
    (hphi : ContDiff ℝ 2 phi) (hMass : Integrable (cotScalarMass n r phi) volume)
    (hEnergy : Integrable (cotScalarReducedForm n r phi) volume)
    (heq : (∫s,cotScalarReducedForm n r phi s)=lam*(∫s,cotScalarMass n r phi s)) :
    ∀s,cotScalarPiconeSquare n r v phi s=0 := by
  obtain ⟨C,_hC0,hC⟩ := cotCutoffBase_deriv_bound
  have hELim := cot_scalar_reduced_cutoff_tendsto n hn r C hC phi hphi hEnergy
  have hMLim := cot_scalar_mass_cutoff_tendsto n r phi hphi hMass
  have hLim : Tendsto (fun R : ℝ=>∫s,cotScalarPiconeSquare n r v (cotCutoffTest R phi) s) atTop (𝓝 (0 : ℝ)) := by
    have hh := hELim.sub ((tendsto_const_nhds (x := lam)).mul hMLim)
    rw [heq,sub_self] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact (cot_scalar_compact_picone_energy_identity n r lam v (cotCutoffTest R phi) hv hpos heig
      (cotCutoffTest_smooth R phi hphi) (cotCutoffTest_hasCompactSupport R hR phi)).symm
  have hMeas (R : ℝ) : Measurable (fun s=>ENNReal.ofReal (cotScalarPiconeSquare n r v (cotCutoffTest R phi) s)) :=
    (cotScalarPiconeSquare_continuous n r v (cotCutoffTest R phi) hv (cotCutoffTest_smooth R phi hphi) hpos).measurable.ennreal_ofReal
  have hFatou := lintegral_liminf_le (μ := (volume : Measure ℝ)) (u := (atTop : Filter ℝ)) hMeas
  have hPoint (s : ℝ) : Tendsto (fun R : ℝ=>ENNReal.ofReal (cotScalarPiconeSquare n r v (cotCutoffTest R phi) s))
      atTop (𝓝 (ENNReal.ofReal (cotScalarPiconeSquare n r v phi s))) := by
    have he : (fun R : ℝ=>ENNReal.ofReal (cotScalarPiconeSquare n r v (cotCutoffTest R phi) s))=ᶠ[atTop]
        fun _=>ENNReal.ofReal (cotScalarPiconeSquare n r v phi s) := by
      filter_upwards [cotCutoffTest_eventually_eq phi hphi s] with R hR
      unfold cotScalarPiconeSquare
      rw [hR.1,hR.2]
    exact tendsto_const_nhds.congr' he.symm
  have hNLim : Tendsto (fun R : ℝ=>∫⁻s,ENNReal.ofReal (cotScalarPiconeSquare n r v (cotCutoffTest R phi) s))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hLim
    simp only [ENNReal.ofReal_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact ofReal_integral_eq_lintegral_ofReal
      (cotScalarPiconeSquare_compact_integrable n r v (cotCutoffTest R phi) hv
        (cotCutoffTest_smooth R phi hphi) hpos (cotCutoffTest_hasCompactSupport R hR phi))
      (ae_of_all _ (cotScalarPiconeSquare_nonneg n r v (cotCutoffTest R phi)))
  have hzero : (∫⁻s,ENNReal.ofReal (cotScalarPiconeSquare n r v phi s))=0 := by
    have hlhs : (fun s=>liminf (fun R : ℝ=>ENNReal.ofReal (cotScalarPiconeSquare n r v (cotCutoffTest R phi) s)) atTop)=
        fun s=>ENNReal.ofReal (cotScalarPiconeSquare n r v phi s) := by
      funext s; exact (hPoint s).liminf_eq
    rw [hlhs,hNLim.liminf_eq] at hFatou
    exact le_antisymm hFatou bot_le
  have hAE := (lintegral_eq_zero_iff ((cotScalarPiconeSquare_continuous n r v phi hv hphi hpos).measurable.ennreal_ofReal)).mp hzero
  have hAE' : cotScalarPiconeSquare n r v phi=ᵐ[volume] (fun _=>0) := by
    filter_upwards [hAE] with s hs
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hs) (cotScalarPiconeSquare_nonneg n r v phi s)
  exact congrFun (MeasureTheory.Measure.eq_of_ae_eq hAE'
    (cotScalarPiconeSquare_continuous n r v phi hv hphi hpos) continuous_const)

/-- Original finite-energy scalar equality states are exactly constant
multiples of the same actual positive ground, with no endpoint amplitude
or divided-profile regularity premise. -/
theorem cot_scalar_finite_equality_exists_ground_multiple (n : ℕ) (hn : 1≤n) (r lam : ℝ) (v phi : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (hpos : ∀t∈Icc (-1 : ℝ) 1,0<v t)
    (heig : DFL.Spectral.LatitudeEigenEquation (n+3) 1 ((n+1 : ℕ) : ℝ) r lam v)
    (hphi : ContDiff ℝ 2 phi) (hMass : Integrable (cotScalarMass n r phi) volume)
    (hEnergy : Integrable (cotScalarReducedForm n r phi) volume)
    (heq : (∫s,cotScalarReducedForm n r phi s)=lam*(∫s,cotScalarMass n r phi s)) :
    ∃c : ℝ,∀s,phi s=c*cotScalarGround v s := by
  have hzero := cot_scalar_finite_equality_picone_zero n hn r lam v phi hv hpos heig hphi hMass hEnergy heq
  have hground := cotScalarGround_smooth v hv
  have hd := hphi.differentiable (by norm_num)
  have hgd := hground.differentiable (by norm_num)
  have hdiv : Differentiable ℝ (fun s=>phi s/cotScalarGround v s) :=
    hd.div hgd (fun s=>(cotScalarGround_positive v hpos s).ne')
  have hderiv : ∀s,deriv (fun t=>phi t/cotScalarGround v t) s=0 := by
    intro s
    have hs := hzero s
    have hp : 0<cotScalarFluxWeight n r s :=
      mul_pos (cotScalarDensity_pos n r s) (inv_pos.mpr (sq_pos_of_pos (cotLineScale_pos s)))
    have hz := (mul_eq_zero.mp hs).resolve_left hp.ne'
    have hz' := sq_eq_zero_iff.mp hz
    rw [deriv_fun_div (hd s) (hgd s) (cotScalarGround_positive v hpos s).ne']
    have hh : cotScalarGround v s≠0 := (cotScalarGround_positive v hpos s).ne'
    field_simp [hh] at hz' ⊢
    nlinarith
  have hconst := is_const_of_deriv_eq_zero hdiv hderiv
  refine ⟨phi 0/cotScalarGround v 0,?_⟩
  intro s
  exact (div_eq_iff (cotScalarGround_positive v hpos s).ne').mp (hconst s 0)

end DFLCotSphere
