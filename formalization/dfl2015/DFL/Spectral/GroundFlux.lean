import DFL.Spectral.AngularComparison

/-!
# The original latitude eigenfunction's one-change flux mechanism

The flux has both physical pole conditions, not arbitrary boundary data.
Its derivative is derived from the manuscript's differential expression.
Every positive smooth eigenfunction with positive linear potential slope
is strictly decreasing in latitude.  No spectral existence or minimizer
identification is assumed to have been proved by this statement.
-/

namespace DFL.Spectral

open Set MeasureTheory

noncomputable section

private theorem latitude_w_pos {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    0 < 1 - t ^ 2 := by
  rcases ht with ⟨hl, hr⟩
  nlinarith

/-- Both-end flux control forces strict negativity when the derivative
has one increasing affine sign change.  The change point is not assumed
to lie inside the interval. -/
theorem flux_neg_of_increasing_affine_derivative
    {j c : ℝ → ℝ} {α β : ℝ} (hβ : 0 < β)
    (hj : ContinuousOn j (Icc (-1 : ℝ) 1))
    (hleft : j (-1) = 0) (hright : j 1 = 0)
    (hc : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < c t)
    (hderiv : ∀ t ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt j (c t * (α + β * t)) t)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : j t < 0 := by
  by_cases hs : α + β * t ≤ 0
  · have hanti : StrictAntiOn j (Icc (-1 : ℝ) t) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      · exact hj.mono (Icc_subset_Icc le_rfl ht.2.le)
      · intro x hx
        rw [interior_Icc] at hx
        have hxfull : x ∈ Ioo (-1 : ℝ) 1 := ⟨hx.1, hx.2.trans ht.2⟩
        rw [(hderiv x hxfull).deriv]
        exact mul_neg_of_pos_of_neg (hc x hxfull) (by
          nlinarith [mul_pos hβ (sub_pos.mpr hx.2)])
    have h := hanti ⟨le_rfl, ht.1.le⟩ ⟨ht.1.le, le_rfl⟩ ht.1
    simpa [hleft] using h
  · have hmono : StrictMonoOn j (Icc t (1 : ℝ)) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      · exact hj.mono (Icc_subset_Icc ht.1.le le_rfl)
      · intro x hx
        rw [interior_Icc] at hx
        have hxfull : x ∈ Ioo (-1 : ℝ) 1 := ⟨ht.1.trans hx.1, hx.2⟩
        rw [(hderiv x hxfull).deriv]
        exact mul_pos (hc x hxfull) (by
          nlinarith [mul_pos hβ (sub_pos.mpr hx.1)])
    have h := hmono ⟨le_rfl, ht.2.le⟩ ⟨ht.2.le, le_rfl⟩ ht.2
    simpa [hright] using h

/-- The exact vanishing coefficient multiplying the latitude derivative. -/
def latitudeFluxFactor (M : ℕ) (r t : ℝ) : ℝ :=
  Real.exp (r * t) * Real.rpow (1 - t ^ 2) ((M : ℝ) / 2)

theorem latitudeFluxFactor_pos (M : ℕ) (r : ℝ) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) : 0 < latitudeFluxFactor M r t :=
  mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (latitude_w_pos ht) _)

theorem latitudeFluxFactor_continuous (M : ℕ) (r : ℝ) :
    Continuous (latitudeFluxFactor M r) := by
  unfold latitudeFluxFactor
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    ((continuous_const.sub (continuous_id.pow 2)).rpow_const
      (fun _ => Or.inr (by positivity)))

@[simp] theorem latitudeFluxFactor_left (M : ℕ) (hM : 0 < M) (r : ℝ) :
    latitudeFluxFactor M r (-1) = 0 := by
  have hm : (M : ℝ) / 2 ≠ 0 := by positivity
  simp [latitudeFluxFactor, Real.zero_rpow hm]

@[simp] theorem latitudeFluxFactor_right (M : ℕ) (hM : 0 < M) (r : ℝ) :
    latitudeFluxFactor M r 1 = 0 := by
  have hm : (M : ℝ) / 2 ≠ 0 := by positivity
  simp [latitudeFluxFactor, Real.zero_rpow hm]

theorem latitudeFluxFactor_eq_weight (M : ℕ) (r : ℝ) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    latitudeFluxFactor M r t = radialWeight M r t * (1 - t ^ 2) := by
  unfold latitudeFluxFactor radialWeight
  simp only [Real.rpow_eq_pow]
  have he : (M : ℝ) / 2 = ((M : ℝ) - 2) / 2 + 1 := by ring
  rw [he, Real.rpow_add_one (ne_of_gt (latitude_w_pos ht)) (((M : ℝ) - 2) / 2)]
  ring

theorem latitudeFluxFactor_eq_weight_Icc (M : ℕ) (hM : 0 < M) (r : ℝ) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    latitudeFluxFactor M r t = radialWeight M r t * (1 - t ^ 2) := by
  have hw : 0 ≤ 1 - t ^ 2 := by
    rcases ht with ⟨hl, hr⟩
    nlinarith
  have he : (M : ℝ) / 2 = ((M : ℝ) - 2) / 2 + 1 := by ring
  have hm : ((M : ℝ) - 2) / 2 + 1 ≠ 0 := by
    rw [← he]
    positivity
  unfold latitudeFluxFactor radialWeight
  simp only [Real.rpow_eq_pow]
  rw [he, Real.rpow_add_one' hw hm]
  ring

theorem latitudeFluxFactor_hasDerivAt (M : ℕ) (r : ℝ) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (latitudeFluxFactor M r)
      (radialWeight M r t * (r * (1 - t ^ 2) - (M : ℝ) * t)) t := by
  have hw : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * t) t := by
    convert (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2) using 1
    simp
  have he := ((hasDerivAt_id t).const_mul r).exp
  have hp := hw.rpow_const (p := (M : ℝ) / 2) (Or.inl (ne_of_gt (latitude_w_pos ht)))
  convert he.mul hp using 1
  unfold radialWeight
  simp only [id_eq, Real.rpow_eq_pow]
  have hexp : (M : ℝ) / 2 - 1 = ((M : ℝ) - 2) / 2 := by ring
  have hexp' : (M : ℝ) / 2 = ((M : ℝ) - 2) / 2 + 1 := by ring
  rw [hexp, hexp', Real.rpow_add_one (ne_of_gt (latitude_w_pos ht)) (((M : ℝ) - 2) / 2)]
  ring

/-- The manuscript's fixed original latitude eigen-equation. -/
def LatitudeEigenEquation (M : ℕ) (b lam0 r lam : ℝ) (v : ℝ → ℝ) : Prop :=
  ∀ t ∈ Ioo (-1 : ℝ) 1,
    -(1 - t ^ 2) * deriv (deriv v) t +
      ((M : ℝ) * t - r * (1 - t ^ 2)) * deriv v t +
      (lam0 + b * r * t) * v t = lam * v t

def latitudeGroundFlux (M : ℕ) (r : ℝ) (v : ℝ → ℝ) (t : ℝ) : ℝ :=
  latitudeFluxFactor M r t * deriv v t

theorem latitudeGroundFlux_hasDerivAt (M : ℕ) (b lam0 r lam : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (heq : LatitudeEigenEquation M b lam0 r lam v)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (latitudeGroundFlux M r v)
      (radialWeight M r t * v t * ((lam0 - lam) + (b * r) * t)) t := by
  have hd : Differentiable ℝ (deriv v) :=
    (hv.deriv' : ContDiff ℝ 1 (deriv v)).differentiable (by norm_num)
  convert (latitudeFluxFactor_hasDerivAt M r ht).mul (hd t).hasDerivAt using 1
  rw [latitudeFluxFactor_eq_weight M r ht]
  have he := heq t ht
  linear_combination radialWeight M r t * he

/-- A positive smooth solution of the original latitude eigen-equation
with `b r>0` strictly decreases; the sign is derived using both poles. -/
theorem positive_latitude_eigenfunction_deriv_neg
    (M : ℕ) (hM : 0 < M) (b lam0 r lam : ℝ) (hbr : 0 < b * r)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hpos : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < v t)
    (heq : LatitudeEigenEquation M b lam0 r lam v)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : deriv v t < 0 := by
  have hj : ContinuousOn (latitudeGroundFlux M r v) (Icc (-1 : ℝ) 1) :=
    ((latitudeFluxFactor_continuous M r).mul
      (hv.deriv' : ContDiff ℝ 1 (deriv v)).continuous).continuousOn
  have hleft : latitudeGroundFlux M r v (-1) = 0 := by
    simp [latitudeGroundFlux, latitudeFluxFactor_left M hM r]
  have hright : latitudeGroundFlux M r v 1 = 0 := by
    simp [latitudeGroundFlux, latitudeFluxFactor_right M hM r]
  have hjneg := flux_neg_of_increasing_affine_derivative hbr hj hleft hright
    (fun x hx => mul_pos (radialWeight_pos M r hx) (hpos x hx))
    (fun x hx => latitudeGroundFlux_hasDerivAt M b lam0 r lam v hv heq hx) ht
  by_contra h
  have hmul := mul_nonneg (latitudeFluxFactor_pos M r ht).le (le_of_not_gt h)
  exact (not_le_of_gt hjneg) hmul

end

end DFL.Spectral
