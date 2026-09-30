import DFL.GCI.AngularMoment2D

/-!
# Explicit original weak GCI solution in ambient dimension two

For `r>0`, the original angular Dirichlet equation admits an elementary
first-order flux formula.  The construction below remains in the original
`AngularEnergyDomain` and is tested against every member of that domain.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

def explicitJ (r : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi, Real.exp (-r * Real.cos θ)

theorem explicitJ_pos (r : ℝ) : 0 < explicitJ r := by
  unfold explicitJ
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((by fun_prop : Continuous (fun θ : ℝ => Real.exp (-r * Real.cos θ))).intervalIntegrable _ _)
  · intro θ _
    exact Real.exp_pos _
  · exact Real.pi_pos

def explicitQ (r θ : ℝ) : ℝ :=
  1 / r - (Real.pi / (r * explicitJ r)) * Real.exp (-r * Real.cos θ)

def explicitG (r θ : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..θ, explicitQ r u

def explicitState (r : ℝ) : AngularState :=
  ⟨explicitG r, explicitQ r⟩

theorem explicitQ_continuous (r : ℝ) : Continuous (explicitQ r) := by
  unfold explicitQ
  fun_prop

theorem explicitQ_boundary_integral_zero (r : ℝ) (hr : 0 < r) :
    (∫ θ in (0 : ℝ)..Real.pi, explicitQ r θ) = 0 := by
  have hJ : explicitJ r ≠ 0 := (explicitJ_pos r).ne'
  have hExp : IntervalIntegrable
      (fun θ : ℝ => Real.exp (-r * Real.cos θ))
      volume (0 : ℝ) Real.pi :=
    (by fun_prop : Continuous (fun θ : ℝ =>
      Real.exp (-r * Real.cos θ))).intervalIntegrable _ _
  change (∫ θ in (0 : ℝ)..Real.pi,
    (1 / r) - (Real.pi / (r * explicitJ r)) *
      Real.exp (-r * Real.cos θ)) = 0
  rw [intervalIntegral.integral_sub (intervalIntegrable_const) (hExp.const_mul _),
    intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_const, sub_zero]
  change Real.pi • (1 / r) -
    Real.pi / (r * explicitJ r) * explicitJ r = 0
  rw [smul_eq_mul]
  field_simp [hr.ne', hJ]
  ring

theorem explicitState_mem_energy (r : ℝ) (hr : 0 < r) :
    AngularEnergyDomain 2 (explicitState r) := by
  unfold AngularEnergyDomain
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (explicitQ_continuous r).intervalIntegrable _ _
  · exact ((explicitQ_continuous r).pow 2).intervalIntegrable _ _
  · intro θ _
    simp [scaledFunction, halfPower, explicitState, explicitG]
  · exact explicitQ_boundary_integral_zero r hr
  · simp

def explicitFlux (r θ : ℝ) : ℝ :=
  Real.exp (r * Real.cos θ) * explicitQ r θ

theorem explicitFlux_formula (r θ : ℝ) :
    explicitFlux r θ =
      Real.exp (r * Real.cos θ) / r -
        Real.pi / (r * explicitJ r) := by
  have hexp : Real.exp (r * Real.cos θ) *
      Real.exp (-r * Real.cos θ) = 1 := by
    rw [← Real.exp_add]
    simp
  unfold explicitFlux explicitQ
  rw [mul_sub]
  rw [show Real.exp (r * Real.cos θ) *
      (Real.pi / (r * explicitJ r) * Real.exp (-r * Real.cos θ)) =
      Real.pi / (r * explicitJ r) by
        calc
          _ = (Real.exp (r * Real.cos θ) *
                Real.exp (-r * Real.cos θ)) *
                (Real.pi / (r * explicitJ r)) := by ring
          _ = _ := by rw [hexp]; ring]
  ring

private theorem explicitWeight_hasDerivAt (r θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (r * Real.cos x))
      (-r * Real.sin θ * Real.exp (r * Real.cos θ)) θ := by
  have harg : HasDerivAt (fun x : ℝ => r * Real.cos x)
      (-r * Real.sin θ) θ := by
    convert (Real.hasDerivAt_cos θ).const_mul r using 1
    ring
  convert harg.exp using 1
  ring

theorem explicitFlux_hasDerivAt (r θ : ℝ) (hr : 0 < r) :
    HasDerivAt (explicitFlux r)
      (-(Real.exp (r * Real.cos θ) * Real.sin θ)) θ := by
  have hfun : explicitFlux r = fun x : ℝ =>
      Real.exp (r * Real.cos x) / r -
        Real.pi / (r * explicitJ r) := by
    funext x
    exact explicitFlux_formula r x
  rw [hfun]
  have h := ((explicitWeight_hasDerivAt r θ).div_const r).sub_const
    (Real.pi / (r * explicitJ r))
  convert h using 1
  field_simp [hr.ne']

theorem explicitFlux_deriv (r θ : ℝ) (hr : 0 < r) :
    deriv (explicitFlux r) θ =
      -(Real.exp (r * Real.cos θ) * Real.sin θ) :=
  (explicitFlux_hasDerivAt r θ hr).deriv

theorem explicitFlux_AC (r : ℝ) :
    AbsolutelyContinuousOnInterval (explicitFlux r)
      (0 : ℝ) Real.pi := by
  have hC1 : ContDiff ℝ 1 (explicitFlux r) := by
    unfold explicitFlux explicitQ
    fun_prop
  obtain ⟨K, hK⟩ :=
    hC1.contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_Icc (0 : ℝ) Real.pi) isCompact_Icc
  have hKu : LipschitzOnWith K (explicitFlux r)
      (Set.uIcc (0 : ℝ) Real.pi) := by
    simpa only [Set.uIcc_of_le Real.pi_pos.le] using hK
  exact hKu.absolutelyContinuousOnInterval

private theorem explicitWeakForm_integrable (r : ℝ)
    (v : AngularState) (hv : AngularEnergyDomain 2 v) :
    IntervalIntegrable
      (fun θ : ℝ => angularWeight 2 r θ *
        (angularDerivative 2 (explicitState r) θ * angularDerivative 2 v θ +
          angularPotential 2 θ * (explicitState r).g θ * v.g θ))
      volume (0 : ℝ) Real.pi := by
  have hflux : Continuous (explicitFlux r) := by
    unfold explicitFlux explicitQ
    fun_prop
  have h := hv.1.continuousOn_mul hflux.continuousOn
  simpa [explicitFlux, explicitState, twoD_angularWeight,
    twoD_angularDerivative, angularPotential, mul_assoc] using h

private theorem explicitSource_integrable (r : ℝ)
    (v : AngularState) (hv : AngularEnergyDomain 2 v) :
    IntervalIntegrable
      (fun θ : ℝ => angularWeight 2 r θ * Real.sin θ * v.g θ)
      volume (0 : ℝ) Real.pi := by
  have hcont : ContinuousOn
      (fun θ : ℝ => Real.exp (r * Real.cos θ) * Real.sin θ * v.g θ)
      (Set.Icc (0 : ℝ) Real.pi) :=
    (by fun_prop : Continuous (fun θ : ℝ =>
      Real.exp (r * Real.cos θ) * Real.sin θ)).continuousOn.mul
      (twoD_g_continuousOn v hv)
  simpa only [twoD_angularWeight] using
    hcont.intervalIntegrable_of_Icc Real.pi_pos.le

private theorem explicitWeakForm_eq_source (r : ℝ) (hr : 0 < r)
    (v : AngularState) (hv : AngularEnergyDomain 2 v) :
    originalWeakForm 2 r (explicitState r) v =
      originalSourcePairing 2 r v := by
  have hzero0 : twoDPrimitive v 0 = 0 := by
    simp [twoDPrimitive]
  have hzeroπ : twoDPrimitive v Real.pi = 0 := hv.2.2.2.1
  have hqae := hv.1.ae_hasDerivAt_integral
  have hleft :
      (∫ θ in (0 : ℝ)..Real.pi,
        explicitFlux r θ * v.scaledDerivative θ) =
      ∫ θ in (0 : ℝ)..Real.pi,
        explicitFlux r θ * deriv (twoDPrimitive v) θ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hqae] with θ hq hθ
    have hθ' : θ ∈ Set.uIcc (0 : ℝ) Real.pi := by
      have hθIoc : θ ∈ Set.Ioc (0 : ℝ) Real.pi := by
        simpa only [Set.uIoc_of_le Real.pi_pos.le] using hθ
      rw [Set.uIcc_of_le Real.pi_pos.le]
      exact ⟨hθIoc.1.le, hθIoc.2⟩
    have hderiv : deriv (twoDPrimitive v) θ = v.scaledDerivative θ :=
      (hq hθ' 0 (by simp [Real.pi_pos.le])).deriv
    rw [hderiv]
  have hIBP := (explicitFlux_AC r).integral_mul_deriv_eq_deriv_mul
    (twoDPrimitive_AC v hv)
  calc
    originalWeakForm 2 r (explicitState r) v =
        ∫ θ in (0 : ℝ)..Real.pi,
          explicitFlux r θ * v.scaledDerivative θ := by
      unfold originalWeakForm
      apply intervalIntegral.integral_congr
      intro θ _
      simp [explicitFlux, explicitState, twoD_angularWeight,
        twoD_angularDerivative, angularPotential, mul_assoc]
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          explicitFlux r θ * deriv (twoDPrimitive v) θ := hleft
    _ = -(∫ θ in (0 : ℝ)..Real.pi,
          deriv (explicitFlux r) θ * twoDPrimitive v θ) := by
      simpa [hzero0, hzeroπ] using hIBP
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          Real.exp (r * Real.cos θ) * Real.sin θ * v.g θ := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθIcc : θ ∈ Set.Icc (0 : ℝ) Real.pi := by
        simpa only [Set.uIcc_of_le Real.pi_pos.le] using hθ
      dsimp only
      rw [explicitFlux_deriv r θ hr,
        ← twoD_reconstruction v hv θ hθIcc]
      ring
    _ = originalSourcePairing 2 r v := by
      unfold originalSourcePairing
      apply intervalIntegral.integral_congr
      intro θ _
      simp [twoD_angularWeight]

/-- The explicit Dirichlet profile satisfies the complete original weak
equation in ambient dimension two, against every represented source-domain
test, without assuming a solution or a sign property. -/
theorem explicit_original_weak_solution_twoD (r : ℝ) (hr : 0 < r) :
    OriginalWeakGCISolution 2 r (explicitState r) := by
  refine ⟨explicitState_mem_energy r hr, ?_⟩
  intro v hv
  exact ⟨explicitWeakForm_integrable r v hv,
    explicitSource_integrable r v hv,
    explicitWeakForm_eq_source r hr v hv⟩

def differenceFromExplicit (r : ℝ) (s : AngularState) : AngularState :=
  ⟨fun θ => s.g θ - explicitG r θ,
   fun θ => s.scaledDerivative θ - explicitQ r θ⟩

private theorem difference_square_integrable (r : ℝ)
    (s : AngularState) (hs : AngularEnergyDomain 2 s) :
    IntervalIntegrable
      (fun θ : ℝ => (s.scaledDerivative θ - explicitQ r θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) Real.pi)
  have hsL1 : Integrable s.scaledDerivative μ := hs.1.1
  have hsL2 : Integrable (fun θ => s.scaledDerivative θ ^ 2) μ := hs.2.1.1
  have heL1 : Integrable (explicitQ r) μ :=
    (explicitQ_continuous r).intervalIntegrable (0 : ℝ) Real.pi |>.1
  have heL2 : Integrable (fun θ => explicitQ r θ ^ 2) μ :=
    ((explicitQ_continuous r).pow 2).intervalIntegrable (0 : ℝ) Real.pi |>.1
  have hsMem : MemLp s.scaledDerivative 2 μ :=
    (memLp_two_iff_integrable_sq hsL1.aestronglyMeasurable).2 hsL2
  have heMem : MemLp (explicitQ r) 2 μ :=
    (memLp_two_iff_integrable_sq heL1.aestronglyMeasurable).2 heL2
  have hdMem := hsMem.sub heMem
  have hdL2 : Integrable
      (fun θ => (s.scaledDerivative θ - explicitQ r θ) ^ 2) μ :=
    (memLp_two_iff_integrable_sq hdMem.aestronglyMeasurable).1 hdMem
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).2 hdL2

private theorem difference_mem_energy (r : ℝ) (hr : 0 < r)
    (s : AngularState) (hs : AngularEnergyDomain 2 s) :
    AngularEnergyDomain 2 (differenceFromExplicit r s) := by
  let e := explicitState r
  have he : AngularEnergyDomain 2 e := explicitState_mem_energy r hr
  unfold AngularEnergyDomain
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hs.1.sub he.1
  · exact difference_square_integrable r s hs
  · intro θ hθ
    have hsθ : IntervalIntegrable s.scaledDerivative volume 0 θ := by
      apply hs.1.mono_set
      rw [Set.uIcc_of_le hθ.1, Set.uIcc_of_le Real.pi_pos.le]
      intro x hx
      exact ⟨hx.1, le_trans hx.2 hθ.2⟩
    have heθ : IntervalIntegrable (explicitQ r) volume 0 θ :=
      (explicitQ_continuous r).intervalIntegrable _ _
    have hsrec := twoD_reconstruction s hs θ hθ
    have herec := twoD_reconstruction e he θ hθ
    simp only [scaledFunction, halfPower, differenceFromExplicit] at *
    norm_num at *
    rw [hsrec]
    rw [intervalIntegral.integral_sub hsθ heθ]
    rfl
  · change (∫ θ in (0 : ℝ)..Real.pi,
      s.scaledDerivative θ - explicitQ r θ) = 0
    rw [intervalIntegral.integral_sub hs.1
      ((explicitQ_continuous r).intervalIntegrable _ _),
      hs.2.2.2.1, explicitQ_boundary_integral_zero r hr]
    ring
  · simp [differenceFromExplicit]

private theorem difference_energy_zero (r : ℝ) (hr : 0 < r)
    (s : AngularState) (hs : OriginalWeakGCISolution 2 r s) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Real.exp (r * Real.cos θ) *
        (s.scaledDerivative θ - explicitQ r θ) ^ 2) = 0 := by
  let e := explicitState r
  let w := differenceFromExplicit r s
  have he : OriginalWeakGCISolution 2 r e :=
    explicit_original_weak_solution_twoD r hr
  have hw : AngularEnergyDomain 2 w := difference_mem_energy r hr s hs.1
  have hsi := (hs.2 w hw).1
  have hei := (he.2 w hw).1
  have heq : originalWeakForm 2 r s w - originalWeakForm 2 r e w = 0 := by
    rw [(hs.2 w hw).2.2, (he.2 w hw).2.2]
    ring
  calc
    _ = ∫ θ in (0 : ℝ)..Real.pi,
        (angularWeight 2 r θ *
          (angularDerivative 2 s θ * angularDerivative 2 w θ +
            angularPotential 2 θ * s.g θ * w.g θ)) -
        (angularWeight 2 r θ *
          (angularDerivative 2 e θ * angularDerivative 2 w θ +
            angularPotential 2 θ * e.g θ * w.g θ)) := by
      apply intervalIntegral.integral_congr
      intro θ _
      simp [twoD_angularWeight, twoD_angularDerivative,
        angularPotential, differenceFromExplicit, explicitState, e, w]
      ring
    _ = originalWeakForm 2 r s w - originalWeakForm 2 r e w := by
      rw [intervalIntegral.integral_sub hsi hei]
      rfl
    _ = 0 := heq

/-- A weak solution in the original represented two-dimensional domain
agrees with the explicit Dirichlet solution at every physical angle. -/
theorem weak_solution_eq_explicit_twoD (r : ℝ) (hr : 0 < r)
    (s : AngularState) (hs : OriginalWeakGCISolution 2 r s)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    s.g θ = explicitG r θ := by
  let e := explicitState r
  let w := differenceFromExplicit r s
  have he : OriginalWeakGCISolution 2 r e :=
    explicit_original_weak_solution_twoD r hr
  have hw : AngularEnergyDomain 2 w := difference_mem_energy r hr s hs.1
  have hsi := (hs.2 w hw).1
  have hei := (he.2 w hw).1
  have henergyInt : IntervalIntegrable
      (fun θ : ℝ => Real.exp (r * Real.cos θ) *
        (s.scaledDerivative θ - explicitQ r θ) ^ 2)
      volume (0 : ℝ) Real.pi := by
    apply (hsi.sub hei).congr
    intro x _
    simp [twoD_angularWeight, twoD_angularDerivative,
      angularPotential, differenceFromExplicit, explicitState, e, w]
    ring
  have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict
      (Set.Ioc (0 : ℝ) Real.pi)]
      (fun θ : ℝ => Real.exp (r * Real.cos θ) *
        (s.scaledDerivative θ - explicitQ r θ) ^ 2) := by
    exact ae_of_all _ (fun x => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
  have hae0 := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
    Real.pi_pos.le hnonneg henergyInt).1
      (difference_energy_zero r hr s hs)
  have hqae : s.scaledDerivative =ᵐ[(volume : Measure ℝ).restrict
      (Set.Ioc (0 : ℝ) Real.pi)] explicitQ r := by
    filter_upwards [hae0] with x hx
    have hp : Real.exp (r * Real.cos x) ≠ 0 := (Real.exp_pos _).ne'
    have hsq : (s.scaledDerivative x - explicitQ r x) ^ 2 = 0 :=
      (mul_eq_zero.mp hx).resolve_left hp
    nlinarith
  have hqaeθ : s.scaledDerivative =ᵐ[(volume : Measure ℝ).restrict
      (Set.Ioc (0 : ℝ) θ)] explicitQ r :=
    ae_restrict_of_ae_restrict_of_subset
      (by intro x hx; exact ⟨hx.1, le_trans hx.2 hθ.2⟩) hqae
  have hqint : (∫ x in (0 : ℝ)..θ, s.scaledDerivative x) =
      ∫ x in (0 : ℝ)..θ, explicitQ r x := by
    apply intervalIntegral.integral_congr_ae
    simpa only [Set.uIoc_of_le hθ.1] using
      (ae_imp_of_ae_restrict hqaeθ)
  calc
    s.g θ = twoDPrimitive s θ := twoD_reconstruction s hs.1 θ hθ
    _ = explicitG r θ := hqint

theorem weak_solution_g_unique_twoD (r : ℝ) (hr : 0 < r)
    (s t : AngularState)
    (hs : OriginalWeakGCISolution 2 r s)
    (ht : OriginalWeakGCISolution 2 r t)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    s.g θ = t.g θ := by
  exact (weak_solution_eq_explicit_twoD r hr s hs θ hθ).trans
    (weak_solution_eq_explicit_twoD r hr t ht θ hθ).symm

theorem weak_solution_coefficient_unique_twoD (r : ℝ) (hr : 0 < r)
    (s t : AngularState)
    (hs : OriginalWeakGCISolution 2 r s)
    (ht : OriginalWeakGCISolution 2 r t) :
    originalGCICoefficient 2 r s = originalGCICoefficient 2 r t := by
  have hden : originalGCIDenominator 2 r s =
      originalGCIDenominator 2 r t := by
    unfold originalGCIDenominator
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hθIcc : θ ∈ Set.Icc (0 : ℝ) Real.pi := by
      simpa only [Set.uIcc_of_le Real.pi_pos.le] using hθ
    dsimp only
    rw [weak_solution_g_unique_twoD r hr s t hs ht θ hθIcc]
  have hnum : originalGCINumerator 2 r s =
      originalGCINumerator 2 r t := by
    unfold originalGCINumerator
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hθIcc : θ ∈ Set.Icc (0 : ℝ) Real.pi := by
      simpa only [Set.uIcc_of_le Real.pi_pos.le] using hθ
    dsimp only
    rw [weak_solution_g_unique_twoD r hr s t hs ht θ hθIcc]
  unfold originalGCICoefficient
  rw [hnum, hden]

end

end DFL.GCI
