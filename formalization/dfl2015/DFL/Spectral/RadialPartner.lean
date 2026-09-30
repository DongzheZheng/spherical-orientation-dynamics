import DFL.Spectral.GroundMoments

/-!
# The manuscript's original radial derivative correspondence

This is the smooth eigen-equation step of `spec:radial-partner`, following
the original proof: `D*D=A`, `DD*=P`, differentiate the radial equation,
and recover its eigenfunction by `D*v/λ`. It does not assert the closed
operator domains or existence/completeness of either spectral realization.
-/

namespace DFL.Spectral
open Set MeasureTheory
open scoped Interval
noncomputable section

/-- The original radial expression, before taking its closed realization. -/
def radialApply (d : ℕ) (r : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(1-t^2)*deriv (deriv f) t + ((d : ℝ)*t-r*(1-t^2))*deriv f t

/-- The adjoint expression in the original weighted latitude spaces. -/
def radialAdjoint (d : ℕ) (r : ℝ) (v : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(1-t^2)*deriv v t + ((d : ℝ)*t-r*(1-t^2))*v t

/-- The derivative partner at the manuscript's parameters M=d+2,b=2. -/
def radialPartnerApply (d : ℕ) (r : ℝ) (v : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(1-t^2)*deriv (deriv v) t +
    (((d : ℝ)+2)*t-r*(1-t^2))*deriv v t + ((d : ℝ)+2*r*t)*v t

def RadialEigenEquation (d : ℕ) (r lam : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ t ∈ Ioo (-1 : ℝ) 1, radialApply d r f t = lam*f t

theorem radial_adjoint_derivative (d : ℕ) (r : ℝ) (f : ℝ → ℝ) :
    radialAdjoint d r (deriv f) = radialApply d r f := rfl

private theorem radial_coefficient_hasDerivAt (d : ℕ) (r t : ℝ) :
    HasDerivAt (fun x : ℝ => (d : ℝ)*x-r*(1-x^2)) ((d : ℝ)+2*r*t) t := by
  convert ((hasDerivAt_id t).const_mul (d : ℝ)).sub
    (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2)).const_mul r)
    using 1
  simp only [id_eq]
  ring

theorem radial_adjoint_hasDerivAt (d : ℕ) (r : ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (t : ℝ) :
    HasDerivAt (radialAdjoint d r v) (radialPartnerApply d r v t) t := by
  have hvd := hv.differentiable (by norm_num)
  have hv1 : ContDiff ℝ 1 (deriv v) := hv.deriv'
  have hwd : HasDerivAt (fun x : ℝ => -(1-x^2)) (2*t) t := by
    convert ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2)).neg
      using 1
    simp only [id_eq]
    ring
  convert (hwd.mul (hv1.differentiable (by norm_num) t).hasDerivAt).add
    ((radial_coefficient_hasDerivAt d r t).mul (hvd t).hasDerivAt) using 1
  dsimp [radialPartnerApply]
  ring

/-- Exact smooth factorization DD*=P; no eigen-equation is assumed. -/
theorem radial_derivative_adjoint (d : ℕ) (r : ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) : deriv (radialAdjoint d r v) = radialPartnerApply d r v := by
  funext t
  exact (radial_adjoint_hasDerivAt d r v hv t).deriv

theorem radial_apply_hasDerivAt (d : ℕ) (r : ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 3 f) (t : ℝ) :
    HasDerivAt (radialApply d r f) (radialPartnerApply d r (deriv f) t) t := by
  exact radial_adjoint_hasDerivAt d r (deriv f) hf.deriv' t

theorem radialPartnerApply_eq_latitude (d : ℕ) (r lam : ℝ) (v : ℝ → ℝ) :
    (∀ t ∈ Ioo (-1 : ℝ) 1, radialPartnerApply d r v t = lam*v t) ↔
      LatitudeEigenEquation (d+2) 2 (d : ℝ) r lam v := by
  simp only [LatitudeEigenEquation, radialPartnerApply, Nat.cast_add, Nat.cast_ofNat]

/-- Differentiating the actual original radial eigen-equation gives the
actual partner eigen-equation, including its physical dimension parameters. -/
theorem radial_eigenfunction_derivative_partner (d : ℕ) (r lam : ℝ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (heq : RadialEigenEquation d r lam f) :
    LatitudeEigenEquation (d+2) 2 (d : ℝ) r lam (deriv f) := by
  apply (radialPartnerApply_eq_latitude d r lam (deriv f)).1
  intro t ht
  have hlocal : radialApply d r f =ᶠ[nhds t] fun x => lam*f x := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    exact heq x hx
  have hd := hlocal.deriv_eq
  rw [(radial_apply_hasDerivAt d r f hf t).deriv,
    ((hf.differentiable (by norm_num) t).hasDerivAt.const_mul lam).deriv] at hd
  exact hd

/-- The original reconstruction formula, with no arbitrary integration
constant: the nonzero eigenvalue determines it. -/
def radialRecover (d : ℕ) (r lam : ℝ) (v : ℝ → ℝ) : ℝ → ℝ :=
  fun t => radialAdjoint d r v t / lam

theorem radial_recover_smooth (d : ℕ) (r lam : ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 3 v) : ContDiff ℝ 2 (radialRecover d r lam v) := by
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  have hvd : ContDiff ℝ 2 (deriv v) := hv.deriv'
  change ContDiff ℝ 2 (fun t =>
    (-(1-t^2)*deriv v t + ((d : ℝ)*t-r*(1-t^2))*v t) / lam)
  fun_prop

theorem radial_recover_hasDerivAt (d : ℕ) (r lam : ℝ) (hlam : lam ≠ 0)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (heq : LatitudeEigenEquation (d+2) 2 (d : ℝ) r lam v)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (radialRecover d r lam v) (v t) t := by
  have hp := (radialPartnerApply_eq_latitude d r lam v).2 heq t ht
  convert (radial_adjoint_hasDerivAt d r v hv t).div_const lam using 1
  rw [hp]
  exact (mul_div_cancel_left₀ (v t) hlam).symm

/-- D(D*v/λ)=v on the original open latitude interval. -/
theorem radial_recover_derivative (d : ℕ) (r lam : ℝ) (hlam : lam ≠ 0)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (heq : LatitudeEigenEquation (d+2) 2 (d : ℝ) r lam v)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    deriv (radialRecover d r lam v) t = v t :=
  (radial_recover_hasDerivAt d r lam hlam v hv heq ht).deriv

/-- Recovering from an actual partner eigenfunction satisfies the original
radial equation. Thus both original differential equations are intertwined. -/
theorem partner_eigenfunction_recovers_radial (d : ℕ) (r lam : ℝ) (hlam : lam ≠ 0)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (heq : LatitudeEigenEquation (d+2) 2 (d : ℝ) r lam v) :
    RadialEigenEquation d r lam (radialRecover d r lam v) := by
  intro t ht
  have hlocal : deriv (radialRecover d r lam v) =ᶠ[nhds t] v := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    exact radial_recover_derivative d r lam hlam v hv heq hx
  have hdd := hlocal.deriv_eq
  dsimp [radialApply, radialRecover]
  rw [radial_recover_derivative d r lam hlam v hv heq ht, hdd]
  dsimp [radialAdjoint]
  field_simp

/-- D*Df/λ=f for the actual original radial eigenfunction. -/
theorem radial_recover_derivative_eigenfunction (d : ℕ) (r lam : ℝ) (hlam : lam ≠ 0)
    (f : ℝ → ℝ) (heq : RadialEigenEquation d r lam f)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    radialRecover d r lam (deriv f) t = f t := by
  change radialApply d r f t / lam = f t
  rw [heq t ht]
  exact mul_div_cancel_left₀ (f t) hlam

theorem radial_flux_eq_shift_weight (d : ℕ) (r t : ℝ) :
    latitudeFluxFactor d r t = radialWeight (d+2) r t := by
  unfold latitudeFluxFactor radialWeight
  congr 2
  push_cast
  ring

private theorem radial_flux_product_hasDerivAt (d : ℕ) (r : ℝ) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun x => latitudeFluxFactor d r x * v x)
      (-(radialWeight d r t * radialAdjoint d r v t)) t := by
  convert (latitudeFluxFactor_hasDerivAt d r ht).mul
    (hv.differentiable (by norm_num) t).hasDerivAt using 1
  rw [latitudeFluxFactor_eq_weight d r ht]
  dsimp [radialAdjoint]
  ring

/-- The original two-pole flux identity: the reconstruction has mean zero
in the original radial measure, without an added mean-zero assumption. -/
theorem radial_adjoint_weighted_mean_zero (d : ℕ) (hd : 2 ≤ d) (r : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) :
    (∫ t in (-1 : ℝ)..1, radialWeight d r t * radialAdjoint d r v t) = 0 := by
  have hvc : Continuous (radialAdjoint d r v) := by
    have hv1 : ContDiff ℝ 1 (deriv v) := hv.deriv'
    change Continuous (fun t => -(1-t^2)*deriv v t + ((d : ℝ)*t-r*(1-t^2))*v t)
    fun_prop
  have hi := ((radialWeight_continuous_ge_two d hd r).mul hvc).intervalIntegrable
    (μ := volume) (-1 : ℝ) 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
    ((latitudeFluxFactor_continuous d r).mul hv.continuous).continuousOn
    (fun t ht => radial_flux_product_hasDerivAt d r v hv ht) hi.neg
  have hd0 : 0 < d := by omega
  simpa [latitudeFluxFactor_left d hd0 r, latitudeFluxFactor_right d hd0 r,
    intervalIntegral.integral_neg] using hFTC

theorem radial_recover_weighted_mean_zero (d : ℕ) (hd : 2 ≤ d) (r lam : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) :
    (∫ t in (-1 : ℝ)..1, radialWeight d r t * radialRecover d r lam v t) = 0 := by
  simp only [radialRecover, ← mul_div_assoc, intervalIntegral.integral_div]
  rw [radial_adjoint_weighted_mean_zero d hd r v hv, zero_div]

/-- The adjoint formula is verified against the actual pair of original
latitude measures p₀ and p₁, with the genuine vanishing pole boundary term. -/
theorem radial_adjoint_green_identity (d : ℕ) (hd : 2 ≤ d) (r : ℝ)
    (f v : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hv : ContDiff ℝ 2 v) :
    (∫ t in (-1 : ℝ)..1, radialWeight d r t * f t * radialAdjoint d r v t) =
      ∫ t in (-1 : ℝ)..1, radialWeight (d+2) r t * deriv f t * v t := by
  have hdc : Continuous (deriv f) := (hf.deriv' : ContDiff ℝ 1 (deriv f)).continuous
  have hvc : Continuous (radialAdjoint d r v) := by
    have hv1 : ContDiff ℝ 1 (deriv v) := hv.deriv'
    change Continuous (fun t => -(1-t^2)*deriv v t + ((d : ℝ)*t-r*(1-t^2))*v t)
    fun_prop
  have hi := (((radialWeight_continuous_ge_two d hd r).mul hf.continuous).mul hvc).intervalIntegrable
    (μ := volume) (-1 : ℝ) 1
  have hj := (((radialWeight_continuous_ge_two (d+2) (by omega) r).mul hdc).mul
    hv.continuous).intervalIntegrable (μ := volume) (-1 : ℝ) 1
  have hderiv : ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun x => latitudeFluxFactor d r x * v x * f x)
        (radialWeight (d+2) r t * deriv f t * v t -
          radialWeight d r t * f t * radialAdjoint d r v t) t := by
    intro t ht
    convert (radial_flux_product_hasDerivAt d r v hv ht).mul
      (hf.differentiable (by norm_num) t).hasDerivAt using 1
    rw [radial_flux_eq_shift_weight d r t]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
    (((latitudeFluxFactor_continuous d r).mul hv.continuous).mul hf.continuous).continuousOn
    hderiv (hj.sub hi)
  have hd0 : 0 < d := by omega
  simp only [Pi.mul_apply, latitudeFluxFactor_left d hd0 r, latitudeFluxFactor_right d hd0 r,
    zero_mul, sub_self] at hFTC
  change IntervalIntegrable (fun t => radialWeight d r t*f t*radialAdjoint d r v t)
    volume (-1 : ℝ) 1 at hi
  change IntervalIntegrable (fun t => radialWeight (d+2) r t*deriv f t*v t)
    volume (-1 : ℝ) 1 at hj
  rw [intervalIntegral.integral_sub hj hi] at hFTC
  linarith

end
end DFL.Spectral
