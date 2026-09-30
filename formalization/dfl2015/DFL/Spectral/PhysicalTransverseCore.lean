import DFL.Spectral.PhysicalLatitudeCore

/-!
# The actual first transverse sphere core and amplitude form

This proves the original physical first-harmonic restriction, for ambient
smooth functions `xᵢ v(x₀)`, with `i ≠ 0`. The tangent gradient is calculated
on the original sphere; orthogonal coordinate swaps preserving the field
axis yield its weighted second-moment latitude slice. The final pole-flux
integration by parts is the manuscript's `spec:amplitude-form-identity`
with ℓ=1. No whole-sphere spectral bound or mode ordering is assumed.
-/

namespace DFL.Spectral
open MeasureTheory InnerProductSpace Set Metric
open scoped Interval
noncomputable section

/-- An ambient smooth realization of the original first transverse mode. -/
def transverseCore (d : ℕ) (i : Fin (d+1)) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 1 v) : SphereC1Core d :=
  ⟨fun x => x i*v (x 0),
    (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (i := i) (n := 1)).mul
      (hv.comp (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (i := 0) (n := 1)))⟩

theorem transverseCore_value (d : ℕ) (i : Fin (d+1)) (v : ℝ → ℝ)
    (hv : ContDiff ℝ 1 v) (x : SpherePoint d) :
    coreValue d (transverseCore d i v hv) x =
      sphereCoordinate d i x*v (fieldCoordinate d x) := rfl

private theorem transverse_ambient_gradient (d : ℕ) (i : Fin (d+1))
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) (x : Ambient d) :
    gradient (fun y : Ambient d => y i*v (y 0)) x =
      v (x 0) • EuclideanSpace.single i (1 : ℝ) +
        (x i*deriv v (x 0)) • EuclideanSpace.single 0 (1 : ℝ) := by
  have hvd := hv.differentiable (by norm_num)
  have hc0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d+1))).hasFDerivAt (x := x)
  have hci := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := x)
  have hcomp : HasFDerivAt (fun y : Ambient d => v (y 0))
      (deriv v (x 0) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (d+1))) x := by
    convert ((hvd (x 0)).hasDerivAt.hasFDerivAt).comp x hc0 using 1
    ext z; simp; ring
  have hder := hci.mul hcomp
  have hdual (j : Fin (d+1)) : toDual ℝ (Ambient d) (EuclideanSpace.single j (1 : ℝ)) =
      EuclideanSpace.proj (𝕜 := ℝ) j := by
    ext z
    simpa using EuclideanSpace.inner_single_left j (1 : ℝ) z
  apply (hasGradientAt_iff_hasFDerivAt.mpr ?_).gradient
  convert hder using 1
  rw [map_add, map_smul, map_smul, hdual i, hdual 0]
  ext z
  simp
  ring

/-- The exact intrinsic gradient of the physical transverse test. -/
theorem transverseCore_tangentGradient (d : ℕ) (i : Fin (d+1))
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) (x : SpherePoint d) :
    coreTangentGradient d (transverseCore d i v hv) x =
      v (fieldCoordinate d x) • coordinateTangentGradient d i x +
        (sphereCoordinate d i x*deriv v (fieldCoordinate d x)) •
          coordinateTangentGradient d 0 x := by
  unfold coreTangentGradient transverseCore
  rw [transverse_ambient_gradient d i v hv]
  have hi : inner ℝ (EuclideanSpace.single i (1 : ℝ)) x.1 = x.1 i := by
    simpa using EuclideanSpace.inner_single_left i (1 : ℝ) x.1
  have h0 : inner ℝ (EuclideanSpace.single 0 (1 : ℝ)) x.1 = x.1 0 := by
    simpa using EuclideanSpace.inner_single_left 0 (1 : ℝ) x.1
  simp only [inner_add_left, real_inner_smul_left, hi, h0,
    coordinateTangentGradient, sphereCoordinate, fieldCoordinate]
  module

private theorem coordinateTangentGradient_inner_field (d : ℕ) (i : Fin (d+1))
    (hi : i ≠ 0) (x : SpherePoint d) :
    inner ℝ (coordinateTangentGradient d i x) (coordinateTangentGradient d 0 x) =
      -sphereCoordinate d i x*fieldCoordinate d x := by
  have hx : inner ℝ x.1 x.1 = 1 := by
    have hn : ‖(x.1 : Ambient d)‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using x.2
    rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hia : inner ℝ (EuclideanSpace.single i (1 : ℝ)) x.1 = x.1 i := by
    simpa using EuclideanSpace.inner_single_left i (1 : ℝ) x.1
  have h0a : inner ℝ x.1 (EuclideanSpace.single 0 (1 : ℝ)) = x.1 0 := by
    calc
      _ = inner ℝ (EuclideanSpace.single 0 (1 : ℝ)) x.1 := real_inner_comm _ _
      _ = x.1 0 := by simpa using EuclideanSpace.inner_single_left 0 (1 : ℝ) x.1
  have hi0 : inner ℝ (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single 0 (1 : ℝ) : Ambient d) = 0 := by
    simpa [hi] using EuclideanSpace.inner_single_left i (1 : ℝ)
      (EuclideanSpace.single 0 (1 : ℝ) : Ambient d)
  simp only [coordinateTangentGradient, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, hia, h0a, hi0, hx,
    sphereCoordinate, fieldCoordinate]
  ring

/-- Pointwise physical energy before the amplitude integration by parts. -/
theorem transverseCore_energy_pointwise (d : ℕ) (i : Fin (d+1)) (hi : i ≠ 0)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) (x : SpherePoint d) :
    ‖coreTangentGradient d (transverseCore d i v hv) x‖^2 =
      (v (fieldCoordinate d x))^2 + (sphereCoordinate d i x)^2 *
        ((1-(fieldCoordinate d x)^2)*(deriv v (fieldCoordinate d x))^2 -
          (v (fieldCoordinate d x))^2 -
          2*fieldCoordinate d x*v (fieldCoordinate d x)*deriv v (fieldCoordinate d x)) := by
  rw [transverseCore_tangentGradient, norm_add_sq_real]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_left, real_inner_smul_right,
    coordinateTangentGradient_norm_sq, coordinateTangentGradient_inner_field d i hi]
  simp only [sphereCoordinate, fieldCoordinate]
  ring

private theorem continuous_sphere_integrable (d : ℕ) (r : ℝ)
    {f : SpherePoint d → ℝ} (hf : Continuous f) : Integrable f (alignedMeasure d r) := by
  letI : IsProbabilityMeasure (alignedMeasure d r) := alignedMeasure_probability d r
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ (fun x => hC x (mem_univ x)))

private theorem fieldCoordinate_swap_transverse (d : ℕ) (i j : Fin (d+1))
    (hi : i ≠ 0) (hj : j ≠ 0) (x : SpherePoint d) :
    fieldCoordinate d (sphereIsometry d (coordinateSwap d i j) x) = fieldCoordinate d x := by
  simp [fieldCoordinate, sphereIsometry, coordinateSwap, Equiv.piCongrLeft'_apply,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hj)]

/-- Axis-fixing orthogonal symmetry gives equal weighted transverse moments. -/
theorem transverse_weighted_square_integral_eq (d : ℕ) (r : ℝ)
    (i j : Fin (d+1)) (hi : i ≠ 0) (hj : j ≠ 0) (F : ℝ → ℝ) :
    (∫ x : SpherePoint d, (sphereCoordinate d i x)^2*F (fieldCoordinate d x) ∂alignedMeasure d r) =
      ∫ x : SpherePoint d, (sphereCoordinate d j x)^2*F (fieldCoordinate d x) ∂alignedMeasure d r := by
  unfold alignedMeasure
  rw [integral_tilted, integral_tilted]
  simp only [smul_eq_mul]
  have h := (sphereIsometry_measurePreserving d (coordinateSwap d i j)).integral_comp'
    (fun x : SpherePoint d =>
      (Real.exp (r*fieldCoordinate d x) / ∫ y : SpherePoint d,
        Real.exp (r*fieldCoordinate d y) ∂surfaceMeasure d) *
          ((sphereCoordinate d i x)^2*F (fieldCoordinate d x)))
  change (∫ x : SpherePoint d,
      (Real.exp (r*fieldCoordinate d (sphereIsometry d (coordinateSwap d i j) x)) /
        ∫ y : SpherePoint d, Real.exp (r*fieldCoordinate d y) ∂surfaceMeasure d) *
      ((sphereCoordinate d i (sphereIsometry d (coordinateSwap d i j) x))^2*
        F (fieldCoordinate d (sphereIsometry d (coordinateSwap d i j) x))) ∂surfaceMeasure d) = _ at h
  simp_rw [fieldCoordinate_swap_transverse d i j hi hj, sphereCoordinate_swap d i j] at h
  exact h.symm

/-- Exact second-moment latitude slice under the original vMF measure. -/
theorem transverse_weighted_square_slice (d : ℕ) (hd : 0 < d) (r : ℝ)
    (i : Fin (d+1)) (hi : i ≠ 0) (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ x : SpherePoint d, (sphereCoordinate d i x)^2*F (fieldCoordinate d x) ∂alignedMeasure d r) =
      (∫ x : SpherePoint d, (1-(fieldCoordinate d x)^2)*F (fieldCoordinate d x)
        ∂alignedMeasure d r)/(d : ℝ) := by
  have hint (j : Fin (d+1)) : Integrable (fun x : SpherePoint d =>
      (sphereCoordinate d j x)^2*F (fieldCoordinate d x)) (alignedMeasure d r) :=
    continuous_sphere_integrable d r
      (((sphereCoordinate_continuous d j).pow 2).mul (hF.comp (fieldCoordinate_continuous d)))
  have hpoint (x : SpherePoint d) : (∑ j : Fin d, (sphereCoordinate d j.succ x)^2) =
      1-(fieldCoordinate d x)^2 := by
    have hh := sphereCoordinate_sq_sum_eq_one d x
    rw [Fin.sum_univ_succ] at hh
    change (fieldCoordinate d x)^2 + (∑ j : Fin d, (sphereCoordinate d j.succ x)^2) = 1 at hh
    linarith
  let J : ℝ := ∫ x : SpherePoint d, (sphereCoordinate d i x)^2*F (fieldCoordinate d x) ∂alignedMeasure d r
  have hsum : (d : ℝ)*J = ∫ x : SpherePoint d,
      (1-(fieldCoordinate d x)^2)*F (fieldCoordinate d x) ∂alignedMeasure d r := by
    calc
      _ = ∑ j : Fin d, ∫ x : SpherePoint d,
          (sphereCoordinate d j.succ x)^2*F (fieldCoordinate d x) ∂alignedMeasure d r := by
        have heq : (∑ j : Fin d, ∫ x : SpherePoint d,
            (sphereCoordinate d j.succ x)^2*F (fieldCoordinate d x) ∂alignedMeasure d r) = ∑ _j : Fin d, J := by
          apply Finset.sum_congr rfl
          intro j _
          exact transverse_weighted_square_integral_eq d r j.succ i (Fin.succ_ne_zero j) hi F
        rw [heq]; simp [nsmul_eq_mul]
      _ = ∫ x : SpherePoint d, ∑ j : Fin d,
          (sphereCoordinate d j.succ x)^2*F (fieldCoordinate d x) ∂alignedMeasure d r := by
        symm; exact integral_finset_sum _ (fun j _ => hint j.succ)
      _ = _ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by dsimp only; rw [← Finset.sum_mul, hpoint x])
  exact (eq_div_iff (show (d : ℝ) ≠ 0 by positivity)).2 (by simpa [J, mul_comm] using hsum)

/-- The original physical norm has exactly the first-amplitude latitude weight. -/
theorem transverseCore_norm_integral (k : ℕ) (r : ℝ) (i : Fin (k+2+1)) (hi : i ≠ 0)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) :
    (∫ x : SpherePoint (k+2), (coreValue (k+2) (transverseCore (k+2) i v hv) x)^2
      ∂alignedMeasure (k+2) r) =
      (∫ t in (-1 : ℝ)..1, radialWeight (k+2) r t*(1-t^2)*(v t)^2) /
        ((k+2 : ℝ)*(∫ t in (-1 : ℝ)..1, radialWeight (k+2) r t)) := by
  simp_rw [transverseCore_value, mul_pow]
  rw [transverse_weighted_square_slice (k+2) (by omega) r i hi (fun t => (v t)^2) (hv.continuous.pow 2)]
  rw [aligned_latitude_integral k r (fun t => (1-t^2)*(v t)^2)
    ((continuous_const.sub (continuous_id.pow 2)).mul (hv.continuous.pow 2))]
  rw [div_div]
  congr 1
  · apply intervalIntegral.integral_congr
    intro t _; ring
  · push_cast; ring

/-- Energy slice obtained from the actual global gradient and the proved
axis-preserving second moments, before the manuscript's pole-flux step. -/
theorem transverseCore_energy_slice (k : ℕ) (r : ℝ) (i : Fin (k+2+1)) (hi : i ≠ 0)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) :
    coreEnergy (k+2) r (transverseCore (k+2) i v (hv.of_le (by norm_num))) =
      (∫ t in (-1 : ℝ)..1, radialWeight (k+2) r t*
        ((v t)^2+(1-t^2)/(k+2 : ℝ)*
          ((1-t^2)*(deriv v t)^2-(v t)^2-2*t*v t*deriv v t))) /
      (∫ t in (-1 : ℝ)..1, radialWeight (k+2) r t) := by
  have hd : Continuous (deriv v) := (hv.deriv' : ContDiff ℝ 1 (deriv v)).continuous
  let A : ℝ → ℝ := fun t => (1-t^2)*(deriv v t)^2-(v t)^2-2*t*v t*deriv v t
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hint1 : Integrable (fun x : SpherePoint (k+2) => (v (fieldCoordinate (k+2) x))^2)
      (alignedMeasure (k+2) r) := continuous_sphere_integrable (k+2) r
    ((hv.continuous.comp (fieldCoordinate_continuous (k+2))).pow 2)
  have hint2 : Integrable (fun x : SpherePoint (k+2) =>
      (sphereCoordinate (k+2) i x)^2*A (fieldCoordinate (k+2) x))
      (alignedMeasure (k+2) r) := continuous_sphere_integrable (k+2) r
    (((sphereCoordinate_continuous (k+2) i).pow 2).mul
      (hA.comp (fieldCoordinate_continuous (k+2))))
  have hint3 : Integrable (fun x : SpherePoint (k+2) =>
      (1-(fieldCoordinate (k+2) x)^2)*A (fieldCoordinate (k+2) x))
      (alignedMeasure (k+2) r) := continuous_sphere_integrable (k+2) r
    (((continuous_const.sub ((fieldCoordinate_continuous (k+2)).pow 2))).mul
      (hA.comp (fieldCoordinate_continuous (k+2))))
  unfold coreEnergy
  simp_rw [transverseCore_energy_pointwise (k+2) i hi]
  change (∫ x : SpherePoint (k+2), (v (fieldCoordinate (k+2) x))^2+
    (sphereCoordinate (k+2) i x)^2*A (fieldCoordinate (k+2) x) ∂alignedMeasure (k+2) r) = _
  rw [integral_add hint1 hint2,
    transverse_weighted_square_slice (k+2) (by omega) r i hi A hA]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  have hcomb : (∫ x : SpherePoint (k+2), (v (fieldCoordinate (k+2) x))^2 ∂alignedMeasure (k+2) r)+
      (∫ x : SpherePoint (k+2), (1-(fieldCoordinate (k+2) x)^2)*A (fieldCoordinate (k+2) x)
        ∂alignedMeasure (k+2) r)/(k+2 : ℝ) =
      ∫ x : SpherePoint (k+2),
        (v (fieldCoordinate (k+2) x))^2+(1-(fieldCoordinate (k+2) x)^2)/(k+2 : ℝ)*
          A (fieldCoordinate (k+2) x) ∂alignedMeasure (k+2) r := by
    rw [← integral_div, ← integral_add hint1 (hint3.div_const _)]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by dsimp only; ring)
  rw [hcomb]
  exact aligned_latitude_integral k r (fun t => (v t)^2+(1-t^2)/(k+2 : ℝ)*A t)
    ((hv.continuous.pow 2).add (((continuous_const.sub (continuous_id.pow 2)).div_const _).mul hA))

private theorem first_amplitude_weight (d : ℕ) (r t : ℝ) :
    radialWeight (d+2) r t = latitudeFluxFactor d r t := by
  unfold radialWeight latitudeFluxFactor
  have he : (((d+2 : ℕ) : ℝ)-2)/2 = (d : ℝ)/2 := by push_cast; ring
  rw [he]

/-- The exact ℓ=1 pole-flux integration by parts from the original amplitude
identity. Both boundary terms vanish by their actual sine-power coefficient. -/
theorem first_transverse_amplitude_identity (d : ℕ) (hd : 2 ≤ d) (r : ℝ)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) :
    (∫ t in (-1 : ℝ)..1, radialWeight d r t*
      ((v t)^2+(1-t^2)/(d : ℝ)*
        ((1-t^2)*(deriv v t)^2-(v t)^2-2*t*v t*deriv v t))) =
      (∫ t in (-1 : ℝ)..1, radialWeight (d+2) r t*
        ((1-t^2)*(deriv v t)^2+((d : ℝ)+r*t)*(v t)^2))/(d : ℝ) := by
  have hdpos : 0 < d := by omega
  have hdreal : (d : ℝ) ≠ 0 := by positivity
  have hdv : Continuous (deriv v) := (hv.deriv' : ContDiff ℝ 1 (deriv v)).continuous
  have hvd := hv.differentiable (by norm_num)
  let A : ℝ → ℝ := fun t => radialWeight d r t*
    ((v t)^2+(1-t^2)/(d : ℝ)*
      ((1-t^2)*(deriv v t)^2-(v t)^2-2*t*v t*deriv v t))
  let B : ℝ → ℝ := fun t => radialWeight (d+2) r t*
    ((1-t^2)*(deriv v t)^2+((d : ℝ)+r*t)*(v t)^2)
  let F : ℝ → ℝ := fun t => -latitudeFluxFactor d r t*t*(v t)^2
  have hA : Continuous A := by
    have hp := radialWeight_continuous_ge_two d hd r
    dsimp [A]; fun_prop
  have hB : Continuous B := by
    have hp := radialWeight_continuous_ge_two (d+2) (by omega) r
    dsimp [B]; fun_prop
  have hF : Continuous F := by
    have hp := latitudeFluxFactor_continuous d r
    dsimp [F]; fun_prop
  have hderiv : ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt F ((d : ℝ)*A t-B t) t := by
    intro t ht
    convert (((latitudeFluxFactor_hasDerivAt d r ht).mul (hasDerivAt_id t)).mul
      ((hvd t).hasDerivAt.pow 2)).neg using 1
    · funext x
      simp only [F, Pi.neg_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
      ring
    · dsimp [A,B]
      rw [first_amplitude_weight, latitudeFluxFactor_eq_weight d r ht]
      field_simp [hdreal]
      ring
  have hiA : IntervalIntegrable A volume (-1 : ℝ) 1 := hA.intervalIntegrable _ _
  have hiB : IntervalIntegrable B volume (-1 : ℝ) 1 := hB.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (-1 : ℝ) ≤ 1) hF.continuousOn hderiv ((hiA.const_mul (d : ℝ)).sub hiB)
  have hzero : (∫ t in (-1 : ℝ)..1, (d : ℝ)*A t-B t) = 0 := by
    simpa [F, latitudeFluxFactor_left d hdpos r, latitudeFluxFactor_right d hdpos r] using hFTC
  rw [intervalIntegral.integral_sub (hiA.const_mul (d : ℝ)) hiB,
    intervalIntegral.integral_const_mul] at hzero
  change (∫ t in (-1 : ℝ)..1, A t) = (∫ t in (-1 : ℝ)..1, B t)/(d : ℝ)
  apply (eq_div_iff hdreal).2
  linarith

/-- The physical global transverse energy equals the manuscript's original
first-amplitude form with p₁=e^(rt)(1-t²)^(d/2), including normalization. -/
theorem transverseCore_energy_integral (k : ℕ) (r : ℝ) (i : Fin (k+2+1)) (hi : i ≠ 0)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) :
    coreEnergy (k+2) r (transverseCore (k+2) i v (hv.of_le (by norm_num))) =
      (∫ t in (-1 : ℝ)..1, radialWeight (k+2+2) r t*
        ((1-t^2)*(deriv v t)^2+((k+2 : ℝ)+r*t)*(v t)^2)) /
      ((k+2 : ℝ)*(∫ t in (-1 : ℝ)..1, radialWeight (k+2) r t)) := by
  have hAmp := first_transverse_amplitude_identity (k+2) (by omega) r v hv
  push_cast at hAmp
  rw [transverseCore_energy_slice k r i hi v hv, hAmp, div_div]

/-- Exact original norm in the same first-amplitude latitude weight p₁. -/
theorem transverseCore_norm_amplitude_integral (k : ℕ) (r : ℝ)
    (i : Fin (k+2+1)) (hi : i ≠ 0) (v : ℝ → ℝ) (hv : ContDiff ℝ 1 v) :
    (∫ x : SpherePoint (k+2), (coreValue (k+2) (transverseCore (k+2) i v hv) x)^2
      ∂alignedMeasure (k+2) r) =
      (∫ t in (-1 : ℝ)..1, radialWeight (k+2+2) r t*(v t)^2) /
      ((k+2 : ℝ)*(∫ t in (-1 : ℝ)..1, radialWeight (k+2) r t)) := by
  rw [transverseCore_norm_integral k r i hi v hv]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have hti : t ∈ Icc (-1 : ℝ) 1 := by simpa using ht
  dsimp only
  rw [first_amplitude_weight (k+2) r t, latitudeFluxFactor_eq_weight_Icc (k+2) (by omega) r hti]

end
end DFL.Spectral
