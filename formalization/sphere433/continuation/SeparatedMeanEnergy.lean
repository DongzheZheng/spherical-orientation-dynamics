import continuation.AngularMeanProjection

/-! The original orthogonal radial/angular energy split, with actual
angular averaging and actual separated Riemannian gradient energy. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Bundle Manifold MeasureTheory Metric Module Set
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DFLAngularMean
namespace DFLSeparatedMean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [CompactSpace M] [Nonempty M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance (h : SmoothRiemannianMetric I M) :
    IsFiniteMeasure (riemannianVolumeMeasure I M h) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace h

/-- Exact angular/radial energy split at every real latitude parameter.
The orthogonal angular projection is computed by the actual volume. -/
theorem separated_angular_mean_energy
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (f b : ℝ → ℝ) (hf : ∀ s, 0 < f s) (hb : ∀ s, 0 < b s)
    (hsep : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y,s) (v,a) (w,c) = (f s)^2*h.inner y v w+(b s)^2*a*c)
    (F : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯) (s : ℝ) :
    (∫ y : M, normGradSqFun gP F (y,s) ∂riemannianVolumeMeasure I M h) =
      ((f s)^2)⁻¹*
        (∫ y : M, normGradSqFun h (fun z : M => angularDeviation h F (z,s)) y
          ∂riemannianVolumeMeasure I M h)+
      ((b s)^2)⁻¹*(angularVolume h*(deriv (angularMean h F) s)^2+
        ∫ y : M, (deriv (fun t : ℝ => angularDeviation h F (y,t)) s)^2
          ∂riemannianVolumeMeasure I M h) := by
  have hFs : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => F (y,s)) :=
    F.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)
  have hEI : Integrable (normGradSqFun h (fun y : M => F (y,s)))
      (riemannianVolumeMeasure I M h) :=
    (normGradSqFun_continuous h hFs).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hDc : Continuous (fun y : M => deriv (fun t : ℝ => F (y,t)) s) :=
    (contMDiff_partial_deriv_snd I F).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hDI : Integrable (fun y : M => (deriv (fun t : ℝ => F (y,t)) s)^2)
      (riemannianVolumeMeasure I M h) :=
    (hDc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp : (fun y : M => normGradSqFun gP F (y,s)) =
      fun y => ((f s)^2)⁻¹*normGradSqFun h (fun z : M => F (z,s)) y+
        ((b s)^2)⁻¹*(deriv (fun t : ℝ => F (y,t)) s)^2 := by
    funext y
    exact DFLProductSlices.separated_gradient_energy_slices h gP f b hf hb hsep F (y,s)
  rw [hp,integral_add (f := fun y : M =>
      ((f s)^2)⁻¹*normGradSqFun h (fun z : M => F (z,s)) y)
    (g := fun y : M => ((b s)^2)⁻¹*(deriv (fun t : ℝ => F (y,t)) s)^2)
      (hEI.const_mul _) (hDI.const_mul _),integral_const_mul,integral_const_mul,
    angular_height_square_split h F s]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with y
  rw [normGradSqFun_def,normGradSqFun_def]
  have hd : gradFun h (fun z : M => angularDeviation h F (z,s)) y =
      gradFun h (fun z : M => F (z,s)) y := angularDeviation_gradient h F s y
  rw [hd]

end DFLSeparatedMean
