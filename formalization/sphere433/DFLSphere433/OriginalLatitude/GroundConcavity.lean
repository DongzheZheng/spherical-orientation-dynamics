import DFLSphere433.OriginalLatitude.GroundHF

/-!
# Strict concavity of the manuscript's original half-density ground energy

This formalizes `spectral.tex`, Lemma `spec:strict-concavity`. The fixed
latitude weight and differential expression are exactly those in GroundHF.
Inputs are existence of positive normalized smooth ground eigenprofiles and
their actual Rayleigh minimum on the smooth core. No energy ordering or
concavity is an input. Equality in the Rayleigh bound is differentiated by
smooth perturbations, so the mixed ground profile satisfies both endpoint
eigen-equations; their subtraction contradicts positivity at two latitudes.

Construction of these ground profiles and identification of their variational
values with the spectrum of the closed full-sphere operator is a separate
existence/domain theorem, and is not asserted by this module.
-/

namespace DFL.Spectral
open Set MeasureTheory
open scoped Interval
noncomputable section

/-- The original fixed half-density expression `B - a*r*t`. -/
def tiltApply (M : ℕ) (lam0 r a : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  halfDensityApply M ((M : ℝ) / 2 - a) lam0 r u

def tiltPair (M : ℕ) (lam0 r a : ℝ) (u v : ℝ → ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1, radialWeight M 0 t * u t * tiltApply M lam0 r a v t

def tiltDefect (M : ℕ) (lam0 r a lam : ℝ) (u v : ℝ → ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1,
    radialWeight M 0 t * u t * (tiltApply M lam0 r a v t - lam * v t)

/-- Genuine ground eigenstate and smooth-core Rayleigh minimum. -/
structure IsTiltGroundProfile (M : ℕ) (lam0 r a lam : ℝ) (u : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ 2 u
  positive : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < u t
  normalized : latitudeNorm M 0 u = 1
  eigen : ∀ t ∈ Icc (-1 : ℝ) 1, tiltApply M lam0 r a u t = lam * u t
  rayleigh : ∀ v : ℝ → ℝ, ContDiff ℝ 2 v →
    lam * latitudeNorm M 0 v ≤ tiltPair M lam0 r a v v

private theorem tiltApply_formula (M : ℕ) (lam0 r a : ℝ) (u : ℝ → ℝ) (t : ℝ) :
    tiltApply M lam0 r a u t = -(1 - t ^ 2) * deriv (deriv u) t +
      (M : ℝ) * t * deriv u t + (lam0 + r ^ 2 * (1 - t ^ 2) / 4 - a * r * t) * u t := by
  unfold tiltApply halfDensityApply halfDensityPotential
  ring

private theorem tiltApply_continuous (M : ℕ) (lam0 r a : ℝ)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) : Continuous (tiltApply M lam0 r a u) :=
  halfDensityApply_continuous M _ lam0 r u hu

private theorem tiltDefect_integrable (M : ℕ) (hM : 2 ≤ M) (lam0 r a lam : ℝ)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    IntervalIntegrable (fun t => radialWeight M 0 t * u t *
      (tiltApply M lam0 r a v t - lam * v t)) volume (-1 : ℝ) 1 :=
  (((radialWeight_continuous_ge_two M hM 0).mul hu.continuous).mul
    ((tiltApply_continuous M lam0 r a v hv).sub
      (continuous_const.mul hv.continuous))).intervalIntegrable _ _

private theorem tiltDefect_eq (M : ℕ) (hM : 2 ≤ M) (lam0 r a lam : ℝ)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) :
    tiltDefect M lam0 r a lam u u =
      tiltPair M lam0 r a u u - lam * latitudeNorm M 0 u := by
  unfold tiltDefect tiltPair latitudeNorm
  have hi : IntervalIntegrable (fun t => radialWeight M 0 t*u t*tiltApply M lam0 r a u t) volume (-1 : ℝ) 1 := (((radialWeight_continuous_ge_two M hM 0).mul hu.continuous).mul
    (tiltApply_continuous M lam0 r a u hu)).intervalIntegrable (μ := volume) (-1 : ℝ) 1
  have hj : IntervalIntegrable (fun t => radialWeight M 0 t*(u t)^2) volume (-1 : ℝ) 1 := ((radialWeight_continuous_ge_two M hM 0).mul
    (hu.continuous.pow 2)).intervalIntegrable (μ := volume) (-1 : ℝ) 1
  calc
    _ = ∫ t in (-1 : ℝ)..1, radialWeight M 0 t * u t * tiltApply M lam0 r a u t -
        lam * (radialWeight M 0 t * (u t)^2) := by
      apply intervalIntegral.integral_congr
      intro t _; ring
    _ = _ := by rw [intervalIntegral.integral_sub hi (hj.const_mul lam),
      intervalIntegral.integral_const_mul]

private theorem tiltDefect_symm (M : ℕ) (hM : 2 ≤ M) (lam0 r a lam : ℝ)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    tiltDefect M lam0 r a lam u v = tiltDefect M lam0 r a lam v u := by
  have hg := halfDensity_green_identity M hM ((M : ℝ)/2-a) lam0 r u v hu hv
  have hi := tiltDefect_integrable M hM lam0 r a lam u v hu hv
  have hj := tiltDefect_integrable M hM lam0 r a lam v u hv hu
  have hid : tiltDefect M lam0 r a lam u v - tiltDefect M lam0 r a lam v u =
      ∫ t in (-1 : ℝ)..1, radialWeight M 0 t *
        (u t * halfDensityApply M ((M : ℝ)/2-a) lam0 r v t -
          v t * halfDensityApply M ((M : ℝ)/2-a) lam0 r u t) := by
    unfold tiltDefect
    rw [← intervalIntegral.integral_sub hi hj]
    apply intervalIntegral.integral_congr
    intro t _; dsimp [tiltApply]; ring
  rw [hg] at hid
  linarith

private theorem tiltApply_perturb (M : ℕ) (lam0 r a z : ℝ) (u v : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    tiltApply M lam0 r a (fun t => u t + z * v t) =
      fun t => tiltApply M lam0 r a u t + z * tiltApply M lam0 r a v t := by
  have hud := hu.differentiable (by norm_num)
  have hvd := hv.differentiable (by norm_num)
  have hu1 : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have hv1 : ContDiff ℝ 1 (deriv v) := hv.deriv'
  have hdu : deriv (fun t => u t + z*v t) = fun t => deriv u t + z*deriv v t := by
    funext t
    have hh := ((hud t).hasDerivAt.add ((hvd t).hasDerivAt.const_mul z)).deriv
    change deriv (fun t => u t + z * v t) t = _ at hh
    exact hh
  funext t
  simp only [tiltApply_formula, hdu]
  have hdd : deriv (fun t => deriv u t+z*deriv v t) t = deriv (deriv u) t+z*deriv (deriv v) t := by
    have hh := ((hu1.differentiable (by norm_num) t).hasDerivAt.add
      ((hv1.differentiable (by norm_num) t).hasDerivAt.const_mul z)).deriv
    change deriv (fun t => deriv u t + z * deriv v t) t = _ at hh
    exact hh
  rw [hdd]
  ring

private theorem tiltDefect_perturb (M : ℕ) (hM : 2 ≤ M) (lam0 r a lam z : ℝ)
    (u v : ℝ → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    tiltDefect M lam0 r a lam (fun t => u t + z*v t) (fun t => u t + z*v t) =
      tiltDefect M lam0 r a lam u u + 2*z*tiltDefect M lam0 r a lam u v +
        z^2*tiltDefect M lam0 r a lam v v := by
  have hii := tiltDefect_integrable M hM lam0 r a lam u u hu hu
  have hij := tiltDefect_integrable M hM lam0 r a lam u v hu hv
  have hji := tiltDefect_integrable M hM lam0 r a lam v u hv hu
  have hjj := tiltDefect_integrable M hM lam0 r a lam v v hv hv
  change (∫ t in (-1 : ℝ)..1, radialWeight M 0 t*(u t+z*v t)*
    (tiltApply M lam0 r a (fun t => u t+z*v t) t-lam*(u t+z*v t))) = _
  rw [tiltApply_perturb M lam0 r a z u v hu hv]
  calc
    _ = ∫ t in (-1 : ℝ)..1,
        radialWeight M 0 t*u t*(tiltApply M lam0 r a u t-lam*u t) +
        z*(radialWeight M 0 t*u t*(tiltApply M lam0 r a v t-lam*v t)) +
        z*(radialWeight M 0 t*v t*(tiltApply M lam0 r a u t-lam*u t)) +
        z^2*(radialWeight M 0 t*v t*(tiltApply M lam0 r a v t-lam*v t)) := by
      apply intervalIntegral.integral_congr
      intro t _; ring
    _ = _ := by
      rw [intervalIntegral.integral_add ((hii.add (hij.const_mul z)).add (hji.const_mul z))
          (hjj.const_mul (z^2)),
        intervalIntegral.integral_add (hii.add (hij.const_mul z)) (hji.const_mul z),
        intervalIntegral.integral_add hii (hij.const_mul z),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      change tiltDefect M lam0 r a lam u u + z*tiltDefect M lam0 r a lam u v +
        z*tiltDefect M lam0 r a lam v u + z^2*tiltDefect M lam0 r a lam v v = _
      rw [tiltDefect_symm M hM lam0 r a lam v u hv hu]
      ring

private theorem linear_coefficient_zero (b c : ℝ) (hc : 0 ≤ c)
    (h : ∀ z : ℝ, 0 ≤ 2*z*b+z^2*c) : b = 0 := by
  have hc1 : 0 < c+1 := by linarith
  have htest := h (-2*b/(c+1))
  have hid : 2*(-2*b/(c+1))*b+(-2*b/(c+1))^2*c = -(4*b^2)/(c+1)^2 := by
    field_simp; ring
  rw [hid] at htest
  have hnum : 0 ≤ -(4*b^2) := by
    have hh := (le_div_iff₀ (sq_pos_of_pos hc1)).1 htest
    simpa using hh
  nlinarith [sq_nonneg b]

/-- Equality in the true Rayleigh bound forces the polarized eigen-equation. -/
theorem tilt_rayleigh_equality_stationary (M : ℕ) (hM : 2 ≤ M) (lam0 r a lam : ℝ)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u)
    (hmin : ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → lam*latitudeNorm M 0 v ≤ tiltPair M lam0 r a v v)
    (heq : tiltPair M lam0 r a u u = lam*latitudeNorm M 0 u) :
    ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → tiltDefect M lam0 r a lam v u = 0 := by
  intro v hv
  have hnonneg : ∀ w : ℝ → ℝ, ContDiff ℝ 2 w → 0 ≤ tiltDefect M lam0 r a lam w w := by
    intro w hw
    rw [tiltDefect_eq M hM lam0 r a lam w hw]
    exact sub_nonneg.mpr (hmin w hw)
  have hzero : tiltDefect M lam0 r a lam u u = 0 := by
    rw [tiltDefect_eq M hM lam0 r a lam u hu, heq]; ring
  have hp : ∀ z : ℝ, 0 ≤ 2*z*tiltDefect M lam0 r a lam u v + z^2*tiltDefect M lam0 r a lam v v := by
    intro z
    have hh := hnonneg (fun t => u t+z*v t) (hu.add (contDiff_const.mul hv))
    rw [tiltDefect_perturb M hM lam0 r a lam z u v hu hv, hzero, zero_add] at hh
    exact hh
  rw [tiltDefect_symm M hM lam0 r a lam v u hv hu]
  exact linear_coefficient_zero _ _ (hnonneg v hv) hp

private theorem tilt_ground_energy (M : ℕ) (lam0 r a lam : ℝ) (u : ℝ → ℝ)
    (hu : IsTiltGroundProfile M lam0 r a lam u) : tiltPair M lam0 r a u u = lam := by
  unfold tiltPair
  calc
    _ = ∫ t in (-1 : ℝ)..1, lam*(radialWeight M 0 t*(u t)^2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hti : t ∈ Icc (-1 : ℝ) 1 := by simpa using ht
      dsimp only
      rw [hu.eigen t hti]; ring
    _ = lam*latitudeNorm M 0 u := by rw [intervalIntegral.integral_const_mul]; rfl
    _ = lam := by rw [hu.normalized, mul_one]

private theorem tiltPair_affine (M : ℕ) (hM : 2 ≤ M) (lam0 r a b s : ℝ)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) :
    tiltPair M lam0 r (s*a+(1-s)*b) u u =
      s*tiltPair M lam0 r a u u+(1-s)*tiltPair M lam0 r b u u := by
  have hi (a : ℝ) : IntervalIntegrable (fun t => radialWeight M 0 t*u t*tiltApply M lam0 r a u t) volume (-1 : ℝ) 1 := (((radialWeight_continuous_ge_two M hM 0).mul hu.continuous).mul
    (tiltApply_continuous M lam0 r a u hu)).intervalIntegrable (μ := volume) (-1 : ℝ) 1
  unfold tiltPair
  calc
    _ = ∫ t in (-1 : ℝ)..1, s*(radialWeight M 0 t*u t*tiltApply M lam0 r a u t)+
        (1-s)*(radialWeight M 0 t*u t*tiltApply M lam0 r b u t) := by
      apply intervalIntegral.integral_congr
      intro t _; simp only [tiltApply_formula]; ring
    _ = _ := by rw [intervalIntegral.integral_add ((hi a).const_mul s) ((hi b).const_mul (1-s)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- A positive profile cannot be a ground eigenprofile at two distinct tilts. -/
theorem positive_profile_not_two_tilts (M : ℕ) (lam0 r a b la lb : ℝ) (hr : 0 < r)
    (hab : a ≠ b) (u : ℝ → ℝ) (hpos : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < u t)
    (ha : ∀ t ∈ Ioo (-1 : ℝ) 1, tiltApply M lam0 r a u t = la * u t)
    (hb : ∀ t ∈ Ioo (-1 : ℝ) 1, tiltApply M lam0 r b u t = lb * u t) : False := by
  have h0a := ha 0 (by norm_num)
  have h0b := hb 0 (by norm_num)
  have h1a := ha (1/2) (by norm_num)
  have h1b := hb (1/2) (by norm_num)
  simp only [tiltApply_formula] at h0a h0b h1a h1b
  have h0u := hpos 0 (by norm_num)
  have h1u := hpos (1/2) (by norm_num)
  have hl : la = lb := by nlinarith [h0a, h0b]
  have hab0 : (a-b)*r*u (1/2) = 0 := by nlinarith [h1a, h1b]
  have hdiff : a-b = 0 := (mul_eq_zero.mp hab0).resolve_right (ne_of_gt h1u)
    |> fun hh => (mul_eq_zero.mp hh).resolve_right (ne_of_gt hr)
  exact hab (sub_eq_zero.mp hdiff)

/-- A mixed ground profile attaining an endpoint Rayleigh minimum satisfies
that endpoint's original differential equation. The residual is a smooth
linear-latitude factor times the known mixed eigenprofile. -/
private theorem tilt_ground_endpoint_equation (M : ℕ) (hM : 2 ≤ M)
    (lam0 r c lc a la : ℝ) (u : ℝ → ℝ)
    (hu : IsTiltGroundProfile M lam0 r c lc u)
    (hmin : ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → la*latitudeNorm M 0 v ≤ tiltPair M lam0 r a v v)
    (heq : tiltPair M lam0 r a u u = la) :
    ∀ t ∈ Ioo (-1 : ℝ) 1, tiltApply M lam0 r a u t = la * u t := by
  let v : ℝ → ℝ := fun t => (lc-la-(a-c)*r*t)*u t
  have hv : ContDiff ℝ 2 v := by
    have hus := hu.smooth
    dsimp [v]; fun_prop
  have heq' : tiltPair M lam0 r a u u = la*latitudeNorm M 0 u := by
    rw [hu.normalized, mul_one]; exact heq
  have hs := tilt_rayleigh_equality_stationary M hM lam0 r a la u hu.smooth hmin heq' v hv
  have hres : ∀ t ∈ Icc (-1 : ℝ) 1, tiltApply M lam0 r a u t-la * u t = v t := by
    intro t ht
    have hh := hu.eigen t ht
    simp only [tiltApply_formula] at hh ⊢
    dsimp [v]
    nlinarith
  have hz : latitudeNorm M 0 v = 0 := by
    unfold tiltDefect at hs
    have hh : (∫ t in (-1 : ℝ)..1, radialWeight M 0 t*v t*(tiltApply M lam0 r a u t-la * u t)) = latitudeNorm M 0 v := by
      unfold latitudeNorm
      apply intervalIntegral.integral_congr
      intro t ht
      have hti : t ∈ Icc (-1 : ℝ) 1 := by simpa using ht
      dsimp only
      rw [hres t hti]; ring
    rw [hh] at hs; exact hs
  intro t ht
  have hvzero : v t = 0 := by
    by_contra hn
    have hp : 0 < latitudeNorm M 0 v := by
      apply intervalIntegral.integral_pos (by norm_num)
        ((radialWeight_continuous_ge_two M hM 0).mul (hv.continuous.pow 2)).continuousOn
      · intro x hx
        exact mul_nonneg (radialWeight_nonneg_Icc M 0 ⟨hx.1.le, hx.2⟩) (sq_nonneg _)
      · exact ⟨t, ⟨ht.1.le, ht.2.le⟩, mul_pos (radialWeight_pos M 0 ht) (sq_pos_of_ne_zero hn)⟩
    linarith
  have hh := hres t ⟨ht.1.le, ht.2.le⟩
  rw [hvzero] at hh
  linarith

/-- Original Rayleigh principle plus actual positive ground eigenstates gives
strict concavity, with equality excluded by subtracting endpoint equations. -/
theorem tilt_ground_energy_strict_concave (M : ℕ) (hM : 2 ≤ M) (lam0 r : ℝ)
    (hr : 0 < r) (E : ℝ → ℝ)
    (hground : ∀ a : ℝ, ∃ u : ℝ → ℝ, IsTiltGroundProfile M lam0 r a (E a) u)
    (a b s : ℝ) (hab : a ≠ b) (hs : 0 < s) (hs1 : s < 1) :
    s*E a+(1-s)*E b < E (s*a+(1-s)*b) := by
  obtain ⟨u, hu⟩ := hground (s*a+(1-s)*b)
  obtain ⟨ua, hua⟩ := hground a
  obtain ⟨ub, hub⟩ := hground b
  have hA := hua.rayleigh u hu.smooth
  have hB := hub.rayleigh u hu.smooth
  rw [hu.normalized, mul_one] at hA hB
  have hC := tilt_ground_energy M lam0 r (s*a+(1-s)*b) (E (s*a+(1-s)*b)) u hu
  rw [tiltPair_affine M hM lam0 r a b s u hu.smooth] at hC
  by_contra hn
  have heA : tiltPair M lam0 r a u u = E a := by nlinarith
  have heB : tiltPair M lam0 r b u u = E b := by nlinarith
  exact positive_profile_not_two_tilts M lam0 r a b (E a) (E b) hr hab u hu.positive
    (tilt_ground_endpoint_equation M hM lam0 r _ _ a (E a) u hu hua.rayleigh heA)
    (tilt_ground_endpoint_equation M hM lam0 r _ _ b (E b) u hu hub.rayleigh heB)

/-- Reflection on the same fixed latitude measure. -/
def reflectProfile (u : ℝ → ℝ) : ℝ → ℝ := fun t => u (-t)

private theorem reflectProfile_smooth (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 2 (reflectProfile u) := hu.comp (contDiff_id.neg)

private theorem reflectProfile_deriv (u : ℝ → ℝ) (hu : Differentiable ℝ u) :
    deriv (reflectProfile u) = fun t => -deriv u (-t) := by
  funext t
  exact ((hu (-t)).hasDerivAt.comp t ((hasDerivAt_id t).neg)).deriv.trans (by ring)

private theorem tiltApply_reflect (M : ℕ) (lam0 r a : ℝ) (u : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u) :
    tiltApply M lam0 r a (reflectProfile u) =
      fun t => tiltApply M lam0 r (-a) u (-t) := by
  have hud := hu.differentiable (by norm_num)
  have hu1 : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have hud1 := hu1.differentiable (by norm_num)
  have hd2 : deriv (deriv (reflectProfile u)) = fun t => deriv (deriv u) (-t) := by
    rw [reflectProfile_deriv u hud]
    funext t
    have hh := ((hud1 (-t)).hasDerivAt.comp t ((hasDerivAt_id t).neg)).neg
    exact hh.deriv.trans (by ring)
  funext t
  simp only [tiltApply_formula]
  rw [hd2, reflectProfile_deriv u hud]
  simp only [reflectProfile]
  ring

private theorem radialWeight_reflect (M : ℕ) (t : ℝ) :
    radialWeight M 0 (-t) = radialWeight M 0 t := by
  simp [radialWeight]

private theorem latitudeNorm_reflect (M : ℕ) (u : ℝ → ℝ) :
    latitudeNorm M 0 (reflectProfile u) = latitudeNorm M 0 u := by
  unfold latitudeNorm
  calc
    _ = ∫ t in (-1 : ℝ)..1, radialWeight M 0 (-t)*(u (-t))^2 := by
      apply intervalIntegral.integral_congr
      intro t _; dsimp only; rw [radialWeight_reflect]; rfl
    _ = _ := by simpa using (intervalIntegral.integral_comp_neg
      (f := fun t => radialWeight M 0 t*(u t)^2) (a := (-1 : ℝ)) (b := (1 : ℝ)))

private theorem tiltPair_reflect (M : ℕ) (lam0 r a : ℝ) (u : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u) :
    tiltPair M lam0 r a (reflectProfile u) (reflectProfile u) =
      tiltPair M lam0 r (-a) u u := by
  unfold tiltPair
  rw [tiltApply_reflect M lam0 r a u hu]
  calc
    _ = ∫ t in (-1 : ℝ)..1, radialWeight M 0 (-t)*u (-t)*tiltApply M lam0 r (-a) u (-t) := by
      apply intervalIntegral.integral_congr
      intro t _; dsimp only; rw [radialWeight_reflect]; rfl
    _ = _ := by simpa using (intervalIntegral.integral_comp_neg
      (f := fun t => radialWeight M 0 t*u t*tiltApply M lam0 r (-a) u t)
      (a := (-1 : ℝ)) (b := (1 : ℝ)))

/-- Reflection derives evenness of the genuine Rayleigh ground energy. -/
theorem tilt_ground_energy_even (M : ℕ) (lam0 r : ℝ) (E : ℝ → ℝ)
    (hground : ∀ a : ℝ, ∃ u : ℝ → ℝ, IsTiltGroundProfile M lam0 r a (E a) u)
    (a : ℝ) : E (-a) = E a := by
  have hle : ∀ a : ℝ, E a ≤ E (-a) := by
    intro b
    obtain ⟨u, hu⟩ := hground (-b)
    obtain ⟨v, hv⟩ := hground b
    have hh := hv.rayleigh (reflectProfile u) (reflectProfile_smooth u hu.smooth)
    rw [latitudeNorm_reflect, hu.normalized, mul_one,
      tiltPair_reflect M lam0 r b u hu.smooth,
      tilt_ground_energy M lam0 r (-b) (E (-b)) u hu] at hh
    exact hh
  exact le_antisymm (by simpa using hle (-a)) (hle a)

/-- The manuscript's strict decrease for nonnegative tilt follows from
reflection and strict concavity, including the zero-tilt endpoint. -/
theorem tilt_ground_energy_strict_decreasing_nonnegative (M : ℕ) (hM : 2 ≤ M)
    (lam0 r : ℝ) (hr : 0 < r) (E : ℝ → ℝ)
    (hground : ∀ a : ℝ, ∃ u : ℝ → ℝ, IsTiltGroundProfile M lam0 r a (E a) u)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) : E b < E a := by
  have hb : 0 < b := by linarith
  let s : ℝ := (a+b)/(2*b)
  have hs : 0 < s := by dsimp [s]; exact div_pos (by linarith) (by positivity)
  have hs1 : s < 1 := by dsimp [s]; apply (div_lt_one (by positivity)).2; linarith
  have hbn : b ≠ -b := by linarith
  have hc : s*b+(1-s)*(-b) = a := by dsimp [s]; field_simp; ring
  have hh := tilt_ground_energy_strict_concave M hM lam0 r hr E hground b (-b) s hbn hs hs1
  rw [hc, tilt_ground_energy_even M lam0 r E hground b] at hh
  nlinarith

/-- For the original pair, M=d+2 and λ₀=d, radial tilt (d-2)/2 is
strictly smaller than transverse tilt d/2. This is the strict first-mode
energy ordering in `spec:mode-ordering`, conditional only on actual ground
profiles and their genuine Rayleigh characterization. -/
theorem original_radial_transverse_ground_ordering (d : ℕ) (hd : 2 ≤ d)
    (r : ℝ) (hr : 0 < r) (E : ℝ → ℝ)
    (hground : ∀ a : ℝ, ∃ u : ℝ → ℝ,
      IsTiltGroundProfile (d+2) (d : ℝ) r a (E a) u) :
    E ((d : ℝ)/2) < E (((d : ℝ)-2)/2) := by
  apply tilt_ground_energy_strict_decreasing_nonnegative (d+2) (by omega)
    (d : ℝ) r hr E hground
  · have hdc : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  · linarith

end
end DFL.Spectral
