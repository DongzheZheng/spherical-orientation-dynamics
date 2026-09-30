import continuation.ProductGradientSlices
import DifferentialGeometry.Analysis.Integration.L2.Parametric.FiberInnerSmoothness

/-! Actual angular mean projection in the original separated-variable
proof. The measure, derivative and orthogonal square splitting are the
genuine compact angular Riemannian objects. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Bundle Manifold MeasureTheory Metric Module Set
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
namespace DFLAngularMean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance (h : SmoothRiemannianMetric I M) :
    IsFiniteMeasure (riemannianVolumeMeasure I M h) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace h

def angularVolume (h : SmoothRiemannianMetric I M) : ℝ :=
  (riemannianVolumeMeasure I M h).real univ

theorem angularVolume_pos (h : SmoothRiemannianMetric I M) : 0 < angularVolume h := by
  let mu := riemannianVolumeMeasure I M h
  let _ : mu.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure h
  have hn : angularVolume h ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨NeZero.ne _,measure_ne_top mu univ⟩
  exact lt_of_le_of_ne ENNReal.toReal_nonneg hn.symm

def angularMean (h : SmoothRiemannianMetric I M)
    (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) (s : ℝ) : ℝ :=
  (∫ y : M, F (y,s) ∂riemannianVolumeMeasure I M h)/angularVolume h

omit [Nonempty M] in
theorem angularMean_smooth (h : SmoothRiemannianMetric I M)
    (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) : ContDiff ℝ ∞ (angularMean h F) :=
  (contDiff_integral_of_jointContMDiff (riemannianVolumeMeasure I M h)
    (fun y s => F (y,s)) F.contMDiff).div_const _

omit [Nonempty M] in
theorem angularMean_hasDerivAt (h : SmoothRiemannianMetric I M)
    (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) (s : ℝ) :
    HasDerivAt (angularMean h F)
      ((∫ y : M, deriv (fun t : ℝ => F (y,t)) s ∂riemannianVolumeMeasure I M h)/
        angularVolume h) s :=
  (hasDerivAt_integral_of_jointContMDiff (riemannianVolumeMeasure I M h)
    (fun y s => F (y,s)) F.contMDiff s).div_const _

def angularDeviation (h : SmoothRiemannianMetric I M)
    (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) :
    C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯ :=
  ⟨fun q => F q-angularMean h F q.2,
    F.contMDiff.sub ((contMDiff_iff_contDiff.mpr (angularMean_smooth h F)).comp contMDiff_snd)⟩

theorem angularDeviation_mean_zero (h : SmoothRiemannianMetric I M)
    (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) (s : ℝ) :
    (∫ y : M, angularDeviation h F (y,s) ∂riemannianVolumeMeasure I M h) = 0 := by
  have hFc : Continuous (fun y : M => F (y,s)) :=
    F.contMDiff.continuous.comp (continuous_id.prodMk continuous_const)
  have hI : Integrable (fun y : M => F (y,s)) (riemannianVolumeMeasure I M h) := hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ y : M, F (y,s)-angularMean h F s ∂riemannianVolumeMeasure I M h) = 0
  rw [integral_sub hI (integrable_const _),integral_const,smul_eq_mul]
  change (∫ y : M, F (y,s) ∂riemannianVolumeMeasure I M h)-
    angularVolume h*((∫ y : M, F (y,s) ∂riemannianVolumeMeasure I M h)/angularVolume h) = 0
  rw [mul_div_cancel₀ _ (ne_of_gt (angularVolume_pos h)),sub_self]

theorem angular_square_split (h : SmoothRiemannianMetric I M)
    (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) (s : ℝ) :
    (∫ y : M, (F (y,s))^2 ∂riemannianVolumeMeasure I M h) =
      angularVolume h*(angularMean h F s)^2+
        ∫ y : M, (angularDeviation h F (y,s))^2 ∂riemannianVolumeMeasure I M h := by
  let c := angularMean h F s
  have hFc : Continuous (fun y : M => F (y,s)) :=
    F.contMDiff.continuous.comp (continuous_id.prodMk continuous_const)
  have hI : Integrable (fun y : M => F (y,s)) (riemannianVolumeMeasure I M h) := hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI2 : Integrable (fun y : M => (F (y,s))^2) (riemannianVolumeMeasure I M h) := (hFc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hid : (fun y : M => (angularDeviation h F (y,s))^2) =
      fun y => (F (y,s))^2-(2*c)*F (y,s)+c^2 := by
    funext y
    change (F (y,s)-c)^2 = _
    ring
  have hJ : Integrable (fun y : M => (F (y,s))^2-(2*c)*F (y,s))
      (riemannianVolumeMeasure I M h) := hI2.sub (hI.const_mul (2*c))
  rw [hid,integral_add (f := fun y : M => (F (y,s))^2-(2*c)*F (y,s))
    (g := fun _ : M => c^2) hJ (integrable_const (c^2)),
    integral_sub (f := fun y : M => (F (y,s))^2)
      (g := fun y : M => (2*c)*F (y,s)) hI2 (hI.const_mul (2*c)),
    integral_const_mul,integral_const,smul_eq_mul]
  have hm : (∫ y : M, F (y,s) ∂riemannianVolumeMeasure I M h) = angularVolume h*c := by
    exact (mul_div_cancel₀ _ (ne_of_gt (angularVolume_pos h))).symm
  rw [hm]
  dsimp only [c,angularVolume]
  ring

omit [Nonempty M] in
theorem angularDeviation_gradient (h : SmoothRiemannianMetric I M)
    (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) (s : ℝ) (y : M) :
    gradientFun h (fun z : M => angularDeviation h F (z,s)) y =
      gradientFun h (fun z : M => F (z,s)) y := by
  have hFs : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun z : M => F (z,s)) :=
    F.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)
  change gradientFun h (fun z : M => F (z,s)-angularMean h F s) y = _
  rw [gradientFun_sub h (hFs.mdifferentiableAt (by simp)) mdifferentiableAt_const,
    gradientFun_const,sub_zero]

/-- Actual smooth height derivative on the product. -/
def heightDerivative (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) :
    C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯ :=
  ⟨fun q => deriv (fun s : ℝ => F (q.1,s)) q.2,contMDiff_partial_deriv_snd I F⟩

omit [Nonempty M] in
theorem angularMean_heightDerivative (h : SmoothRiemannianMetric I M)
    (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) (s : ℝ) :
    angularMean h (heightDerivative F) s = deriv (angularMean h F) s :=
  (angularMean_hasDerivAt h F s).deriv.symm

omit [Nonempty M] in
theorem angularDeviation_hasDerivAt (h : SmoothRiemannianMetric I M)
    (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) (y : M) (s : ℝ) :
    HasDerivAt (fun t : ℝ => angularDeviation h F (y,t))
      (deriv (fun t : ℝ => F (y,t)) s-deriv (angularMean h F) s) s := by
  have hFs : ContDiff ℝ ∞ (fun t : ℝ => F (y,t)) :=
    contMDiff_iff_contDiff.mp (F.contMDiff.comp (contMDiff_const.prodMk contMDiff_id))
  exact ((hFs.differentiable (by simp) s).hasDerivAt).sub
    (((angularMean_smooth h F).differentiable (by simp) s).hasDerivAt)

omit [Nonempty M] in
theorem heightDerivative_angularDeviation (h : SmoothRiemannianMetric I M)
    (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) :
    heightDerivative (angularDeviation h F) = angularDeviation h (heightDerivative F) := by
  ext q
  change deriv (fun s : ℝ => angularDeviation h F (q.1,s)) q.2 =
    deriv (fun s : ℝ => F (q.1,s)) q.2-angularMean h (heightDerivative F) q.2
  rw [angularMean_heightDerivative]
  exact (angularDeviation_hasDerivAt h F q.1 q.2).deriv

/-- Genuine orthogonal split of the height derivative energy. -/
theorem angular_height_square_split (h : SmoothRiemannianMetric I M)
    (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) (s : ℝ) :
    (∫ y : M, (deriv (fun t : ℝ => F (y,t)) s)^2
      ∂riemannianVolumeMeasure I M h) =
      angularVolume h*(deriv (angularMean h F) s)^2+
        ∫ y : M, (deriv (fun t : ℝ => angularDeviation h F (y,t)) s)^2
          ∂riemannianVolumeMeasure I M h := by
  have hh := angular_square_split h (heightDerivative F) s
  rw [angularMean_heightDerivative,← heightDerivative_angularDeviation] at hh
  exact hh

end DFLAngularMean
