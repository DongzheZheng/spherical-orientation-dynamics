import continuation.OriginalTiltGroundExists

/-! Exact ungauging of the actual C² positive latitude ground. These
statements can be applied to the same physical sphere ground used in a
Hellmann--Feynman argument; they do not select a different sphere state. -/
noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped Interval
namespace DFL.Spectral
open DFLSphere

/-- Original weighted amplitude from the original half-density profile. -/
def weightedProfileFromHalfDensity (r : ℝ) (psi : ℝ → ℝ) : ℝ → ℝ :=
  halfDensityLift (-r) psi

theorem weightedProfileFromHalfDensity_smooth (r : ℝ) (psi : ℝ → ℝ)
    (hpsi : ContDiff ℝ 2 psi) :
    ContDiff ℝ 2 (weightedProfileFromHalfDensity r psi) :=
  halfDensityLift_smooth (-r) psi hpsi

theorem weightedProfileFromHalfDensity_positive (r : ℝ) (psi : ℝ → ℝ)
    (hpos : ∀ t ∈ Icc (-1 : ℝ) 1, 0 < psi t) :
    ∀ t ∈ Icc (-1 : ℝ) 1, 0 < weightedProfileFromHalfDensity r psi t := by
  intro t ht
  exact mul_pos (Real.exp_pos _) (hpos t ht)

theorem weightedProfileFromHalfDensity_deriv (r : ℝ) (psi : ℝ → ℝ)
    (hpsi : ContDiff ℝ 2 psi) (t : ℝ) :
    deriv (weightedProfileFromHalfDensity r psi) t =
      Real.exp ((-r/2)*t)*(deriv psi t-r/2*psi t) := by
  rw [weightedProfileFromHalfDensity,halfDensityLift_deriv (-r) psi hpsi t]
  congr 1
  ring

private theorem weightedProfileFromHalfDensity_lift (r : ℝ) (psi : ℝ → ℝ) :
    halfDensityLift r (weightedProfileFromHalfDensity r psi) = psi := by
  funext t
  dsimp [weightedProfileFromHalfDensity,halfDensityLift]
  rw [← mul_assoc,← Real.exp_add]
  have he : r/2*t+(-r)/2*t = 0 := by ring
  rw [he,Real.exp_zero,one_mul]

/-- Exact original weighted eigen-equation for the given half-density
profile. The tilt/amplitude correspondence is `a=M/2-b`. -/
theorem weightedProfileFromHalfDensity_eigen (M : ℕ) (b lam0 r lam : ℝ)
    (psi : ℝ → ℝ) (hpsi : ContDiff ℝ 2 psi)
    (heig : ∀ t ∈ Icc (-1 : ℝ) 1,
      tiltApply M lam0 r ((M : ℝ)/2-b) psi t = lam*psi t) :
    LatitudeEigenEquation M b lam0 r lam (weightedProfileFromHalfDensity r psi) := by
  intro t ht
  let v := weightedProfileFromHalfDensity r psi
  have hv := weightedProfileFromHalfDensity_smooth r psi hpsi
  have happly := halfDensityApply_lift M b lam0 r v hv t
  have hlift : halfDensityLift r v = psi := weightedProfileFromHalfDensity_lift r psi
  rw [hlift] at happly
  have hpsiE : halfDensityApply M b lam0 r psi t = lam*psi t := by
    have hb : (M : ℝ)/2-((M : ℝ)/2-b) = b := by ring
    simpa only [tiltApply,hb] using heig t ⟨ht.1.le,ht.2.le⟩
  apply mul_left_cancel₀ (Real.exp_ne_zero ((r/2)*t))
  calc
    _ = halfDensityApply M b lam0 r psi t := happly.symm
    _ = lam*psi t := hpsiE
    _ = _ := by
      have hid : psi t = Real.exp ((r/2)*t)*v t := (congrFun hlift t).symm
      exact (congrArg (fun z => lam*z) hid).trans (by dsimp [v]; ring)

/-- Both physical pole fluxes force the same given weighted state to be
strictly decreasing when its linear potential slope is positive. -/
theorem positive_tilt_profile_ungauged_deriv_neg (M : ℕ) (hM : 0 < M)
    (b lam0 r lam : ℝ) (hbr : 0 < b*r) (psi : ℝ → ℝ)
    (hpsi : ContDiff ℝ 2 psi) (hpos : ∀ t ∈ Icc (-1 : ℝ) 1, 0 < psi t)
    (heig : ∀ t ∈ Icc (-1 : ℝ) 1,
      tiltApply M lam0 r ((M : ℝ)/2-b) psi t = lam*psi t)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    deriv (weightedProfileFromHalfDensity r psi) t < 0 :=
  positive_latitude_eigenfunction_deriv_neg M hM b lam0 r lam hbr _
    (weightedProfileFromHalfDensity_smooth r psi hpsi)
    (fun x hx => weightedProfileFromHalfDensity_positive r psi hpos x ⟨hx.1.le,hx.2.le⟩)
    (weightedProfileFromHalfDensity_eigen M b lam0 r lam psi hpsi heig) ht

/-- Exact original weighted norm is retained by the actual half-density
map, including both endpoints and every real field parameter. -/
theorem weightedProfileFromHalfDensity_norm (M : ℕ) (r : ℝ) (psi : ℝ → ℝ) :
    latitudeNorm M r (weightedProfileFromHalfDensity r psi) = latitudeNorm M 0 psi := by
  unfold latitudeNorm
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [radialWeight,weightedProfileFromHalfDensity,halfDensityLift]
  simp only [zero_mul,Real.exp_zero,one_mul,pow_two]
  have he : Real.exp (r*t)*(Real.exp ((-r)/2*t)*Real.exp ((-r)/2*t)) = 1 := by
    rw [← Real.exp_add,← Real.exp_add]
    have hz : r*t+((-r)/2*t+(-r)/2*t) = 0 := by ring
    rw [hz,Real.exp_zero]
  calc
    _ = (Real.exp (r*t)*(Real.exp ((-r)/2*t)*Real.exp ((-r)/2*t)))*
        ((1-t*t)^(((M : ℝ)-2)/2)*(psi t*psi t)) := by ring
    _ = _ := by rw [he,one_mul]

/-- Unconditional actual weighted positive eigenstates for all dimensions
M ≥ 2 and every real b,lambda0,r, normalized in the original p(M,r) weight. -/
theorem original_weighted_positive_ground_exists (M : ℕ) (hM : 2 ≤ M)
    (b lam0 r : ℝ) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, 0 < v t) ∧ latitudeNorm M r v = 1 ∧
      LatitudeEigenEquation M b lam0 r
        (roundTiltMinimum (M-2) lam0 r ((M : ℝ)/2-b)) v := by
  obtain ⟨psi,hpsi,hpos⟩ := original_tilt_ground_exists_ge_two M hM lam0 r ((M : ℝ)/2-b)
  refine ⟨weightedProfileFromHalfDensity r psi,
    weightedProfileFromHalfDensity_smooth r psi hpsi.smooth,
    weightedProfileFromHalfDensity_positive r psi hpos,?_,
    weightedProfileFromHalfDensity_eigen M b lam0 r _ psi hpsi.smooth hpsi.eigen⟩
  rw [weightedProfileFromHalfDensity_norm,hpsi.normalized]

/-- The exact original positive weighted eigenstates have the manuscript's
strict flux sign and positive W,K moments, with existence discharged. -/
theorem original_weighted_ground_flux_moments_exists (M : ℕ) (hM : 2 ≤ M)
    (b lam0 r : ℝ) (hb : 0 < b) (hr : 0 < r) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, 0 < v t) ∧ latitudeNorm M r v = 1 ∧
      LatitudeEigenEquation M b lam0 r
        (roundTiltMinimum (M-2) lam0 r ((M : ℝ)/2-b)) v ∧
      (∀ t ∈ Ioo (-1 : ℝ) 1, deriv v t < 0) ∧
      0 < latitudeW M r v ∧ 0 < latitudeK M r v := by
  obtain ⟨v,hv,hpos,hn,heig⟩ := original_weighted_positive_ground_exists M hM b lam0 r
  have hpos' : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < v t := fun t ht => hpos t ⟨ht.1.le,ht.2.le⟩
  refine ⟨v,hv,hpos,hn,heig,?_,latitudeW_pos M hM r v hv.continuous hpos',?_⟩
  · intro t ht
    exact positive_latitude_eigenfunction_deriv_neg M (by omega) b lam0 r _
      (mul_pos hb hr) v hv hpos' heig ht
  · exact latitudeK_pos_of_positive_eigenfunction M hM b lam0 r _
      (mul_pos hb hr) v hv hpos' heig

/-- The normalized original weighted HF integral equals the original
moment expression. No parameter branch or scalar derivative is an input. -/
theorem weighted_HF_integral_eq_rate (M : ℕ) (hM : 2 ≤ M) (b r : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hn : latitudeNorm M r v = 1) :
    (∫ t in (-1 : ℝ)..1, radialWeight M r t *
      (r/2*(1-t^2)+(b-(M : ℝ)/2)*t)*(v t)^2) =
      r/2*latitudeW M r v+(b-(M : ℝ)/2)*latitudeMean M r v := by
  have hA : IntervalIntegrable (fun t => latitudeFluxFactor M r t*(v t)^2) volume (-1 : ℝ) 1 :=
    ((latitudeFluxFactor_continuous M r).mul (hv.continuous.pow 2)).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun t => radialWeight M r t*t*(v t)^2) volume (-1 : ℝ) 1 :=
    (((radialWeight_continuous_ge_two M hM r).mul continuous_id).mul (hv.continuous.pow 2)).intervalIntegrable _ _
  unfold latitudeW latitudeMean
  rw [hn,div_one,div_one]
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hA.const_mul (r/2)) (hB.const_mul (b-(M : ℝ)/2))]
  apply intervalIntegral.integral_congr
  intro t ht
  have htcc : t ∈ Icc (-1 : ℝ) 1 := by simpa using ht
  dsimp only
  rw [latitudeFluxFactor_eq_weight_Icc M (by omega) r htcc]
  ring

/-- A genuine actual state has a strictly positive original HF integral
for the physical range 0<b≤M/2. This asserts the integral sign, not a
parameter derivative without a differentiable eigenbranch. -/
theorem original_weighted_ground_positive_HF_integral_exists (M : ℕ) (hM : 2 ≤ M)
    (b lam0 r : ℝ) (hb : 0 < b) (hbhalf : 2*b ≤ (M : ℝ)) (hr : 0 < r) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, 0 < v t) ∧ latitudeNorm M r v = 1 ∧
      LatitudeEigenEquation M b lam0 r
        (roundTiltMinimum (M-2) lam0 r ((M : ℝ)/2-b)) v ∧
      0 < (∫ t in (-1 : ℝ)..1, radialWeight M r t *
        (r/2*(1-t^2)+(b-(M : ℝ)/2)*t)*(v t)^2) := by
  obtain ⟨v,hv,hpos,hn,heig⟩ := original_weighted_positive_ground_exists M hM b lam0 r
  refine ⟨v,hv,hpos,hn,heig,?_⟩
  rw [weighted_HF_integral_eq_rate M hM b r v hv hn]
  exact positive_eigenfunction_HF_rate_pos M hM b lam0 r _ hb hbhalf hr v hv
    (fun t ht => hpos t ⟨ht.1.le,ht.2.le⟩) heig

/-- Actual first-transverse positive weighted state, all physical d≥1. -/
theorem original_first_transverse_weighted_ground_exists (d : ℕ) (r : ℝ) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, 0 < v t) ∧ latitudeNorm (d+2) r v = 1 ∧
      LatitudeEigenEquation (d+2) 1 (d : ℝ) r
        (roundTiltMinimum d (d : ℝ) r ((d : ℝ)/2)) v := by
  have ha : ((d+2 : ℕ) : ℝ)/2-1 = (d : ℝ)/2 := by push_cast; ring
  simpa only [Nat.add_sub_cancel,ha] using
    original_weighted_positive_ground_exists (d+2) (by omega) 1 (d : ℝ) r

/-- Actual radial-partner positive weighted state, including the d=1
circle partner. Its existence does not require a half-range HF premise. -/
theorem original_radial_partner_weighted_ground_exists (d : ℕ) (r : ℝ) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, 0 < v t) ∧ latitudeNorm (d+2) r v = 1 ∧
      LatitudeEigenEquation (d+2) 2 (d : ℝ) r
        (roundTiltMinimum d (d : ℝ) r (((d : ℝ)-2)/2)) v := by
  have ha : ((d+2 : ℕ) : ℝ)/2-2 = ((d : ℝ)-2)/2 := by push_cast; ring
  simpa only [Nat.add_sub_cancel,ha] using
    original_weighted_positive_ground_exists (d+2) (by omega) 2 (d : ℝ) r

end DFL.Spectral
