import continuation.TransverseWeakH1
import continuation.ClassicalPotentialWeak

/-! The physical drift operator has the actual positive zero mode
exp(r t/2) after the half-density transform, in every sphere dimension. -/
noncomputable section
open Bundle Manifold Metric Module Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Analysis.Laplacian
open DFLSpectralCoordinates DFLLatitudeOperator DFL.Spectral
open DFLSphere

namespace DFLDriftBaseline
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n+1)] [NeZero n]
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩
private instance modelFinrankNeZero : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

/-- The actual half-density zero mode of the original weighted operator. -/
def driftBaseline (p : E) (r : ℝ) (x : sphere (0 : E) 1) : ℝ :=
  Real.exp ((r/2)*⟪p,(x : E)⟫_ℝ)

/-- The actual potential on the physical Sⁿ, with its physical dimension. -/
def driftPotential (n : ℕ) (p : E) (r : ℝ) (x : sphere (0 : E) 1) : ℝ :=
  r^2/4*(1-⟪p,(x : E)⟫_ℝ^2)-r*(n : ℝ)/2*⟪p,(x : E)⟫_ℝ

omit [FiniteDimensional ℝ E] [NeZero n] in
/-- The baseline is genuinely C∞ on the actual physical sphere. -/
theorem driftBaseline_smooth (p : E) (r : ℝ) :
    ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (driftBaseline p r) := by
  have h := Real.contDiff_exp.contMDiff.comp
    ((contMDiff_const : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (fun _ : sphere (0 : E) 1 => r/2)).mul
      (innerCoordFun (n := n) p).contMDiff)
  exact h

omit [FiniteDimensional ℝ E] [Fact (finrank ℝ E = n+1)] [NeZero n] in
theorem driftBaseline_pos (p : E) (r : ℝ) (x : sphere (0 : E) 1) :
    0 < driftBaseline p r x := Real.exp_pos _

omit [FiniteDimensional ℝ E] in
/-- The actual Levi-Civita Schrödinger operator annihilates the positive
baseline. This is a direct coordinate computation, not a spectral premise. -/
theorem driftBaseline_zero_eigen (p : E) (hp : ‖p‖ = 1) (r : ℝ)
    (x : sphere (0 : E) 1) :
    -laplacian (LeviCivita (roundMetric (E := E) (n := n)))
      (roundMetric (E := E) (n := n)) (driftBaseline p r) x +
      driftPotential n p r x*driftBaseline p r x = 0 := by
  have h := latitude_laplacian (n := n) p hp (halfDensityLift r (fun _ => 1))
    (halfDensityLift_smooth r (fun _ => 1) contDiff_const) x
  have he : (fun y : sphere (0 : E) 1 => halfDensityLift r (fun _ => 1) ⟪p,(y : E)⟫_ℝ) =
      driftBaseline p r := by funext y; simp only [halfDensityLift,driftBaseline,mul_one]
  rw [he,halfDensityLift_deriv r (fun _ => 1) contDiff_const,
    halfDensityLift_second_deriv r (fun _ => 1) contDiff_const] at h
  have hd : deriv (fun _ : ℝ => (1 : ℝ)) = fun _ => 0 := by
    funext t
    exact deriv_const t 1
  simp only [hd,deriv_const,zero_add,mul_zero,add_zero,mul_one] at h
  rw [h]
  unfold driftPotential driftBaseline
  ring

/-- The explicit smooth baseline in the actual smooth core. -/
def driftBaselineSmooth (p : E) (r : ℝ) : SmoothScalar (roundMetric (E := E) (n := n)) :=
  ⟨driftBaseline p r,driftBaseline_smooth p r⟩

omit [FiniteDimensional ℝ E] [NeZero n] in
/-- The physical drift potential is a genuine smooth scalar function. -/
theorem driftPotential_smooth (p : E) (r : ℝ) :
    ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (driftPotential n p r) := by
  let t := innerCoordFun (n := n) p
  have ht : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ t := t.contMDiff
  change ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞
    (fun x : sphere (0 : E) 1 => r^2/4*(1-(t x)^2)-r*(n : ℝ)/2*t x)
  exact (contMDiff_const.mul (contMDiff_const.sub (ht.pow 2))).sub (contMDiff_const.mul ht)

/-- The actual physical potential as a smooth manifold map. -/
def driftPotentialMap (p : E) (r : ℝ) : C^∞⟮𝓡 n, sphere (0 : E) 1; ℝ⟯ :=
  ⟨driftPotential n p r,driftPotential_smooth p r⟩

omit [FiniteDimensional ℝ E] [NeZero n] in
/-- The actual physical Schrödinger potential is continuous. -/
theorem driftPotential_continuous (p : E) (r : ℝ) :
    Continuous (driftPotential n p r) := by
  let t := innerCoordFun (n := n) p
  have ht : Continuous t := t.contMDiff.continuous
  change Continuous (fun x : sphere (0 : E) 1 => r^2/4*(1-(t x)^2)-r*(n : ℝ)/2*t x)
  fun_prop

omit [NeZero n] in
/-- The genuine physical potential is an actual bounded L∞ multiplier. -/
theorem driftPotential_memLp_top (p : E) (r : ℝ) :
    MemLp (driftPotential n p r) ∞
      (riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))) := by
  have hfin : IsFiniteMeasure
      (riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace _
  exact (driftPotential_continuous (n := n) p r).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The explicit positive zero mode satisfies the true zero-eigenvalue
identity against every test in the actual full H¹ completion. -/
theorem driftBaseline_weak_zero (p : E) (hp : ‖p‖ = 1) (r : ℝ) :
    ∀ W : H1Compl (roundMetric (E := E) (n := n)),
      potentialForm (H1ComplToLp (roundMetric (E := E) (n := n)))
        (boundedPotentialMultiplication (driftPotential n p r) (driftPotential_memLp_top p r))
        (smoothToH1Compl (roundMetric (E := E) (n := n)) (driftBaselineSmooth p r)) W = 0 := by
  have heig : ∀ x : sphere (0 : E) 1,
      -ΔG (roundMetric (E := E) (n := n)) (driftBaselineSmooth (n := n) p r).toContMDiffMap x+
        driftPotential n p r x*(driftBaselineSmooth (n := n) p r).toFun x =
        0*(driftBaselineSmooth (n := n) p r).toFun x := by
    intro x
    have h := driftBaseline_zero_eigen (n := n) p hp r x
    rw [laplacian_levi_eq _ (driftBaseline_smooth (n := n) p r)] at h
    simpa only [driftBaselineSmooth,SmoothScalar.toContMDiffMap,zero_mul] using h
  simpa only [zero_mul] using DFLClassicalPotentialWeak.smooth_classical_potential_eigen_weak
    (roundMetric (E := E) (n := n)) (driftPotential n p r) (driftPotential_memLp_top p r)
    0 (driftBaselineSmooth p r) heig

/-- The explicit baseline has positive actual L² mass and exactly its
classical energy in the true completion. -/
theorem driftBaseline_exists_nonzero_completion (p : E) (hp : ‖p‖ = 1) (r : ℝ) :
    ∃ U : H1Compl (roundMetric (E := E) (n := n)),
      (H1ComplToLp (roundMetric (E := E) (n := n)) U : sphere (0 : E) 1 → ℝ)
        =ᵐ[riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n))]
          driftBaseline p r ∧
      0 < ‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖ ∧
      ‖U‖^2-‖H1ComplToLp (roundMetric (E := E) (n := n)) U‖^2 =
        ∫ x, (roundMetric (E := E) (n := n)).inner x
          (gradientFun (roundMetric (E := E) (n := n)) (driftBaseline p r) x)
          (gradientFun (roundMetric (E := E) (n := n)) (driftBaseline p r) x)
          ∂riemannianVolumeMeasure (𝓡 n) (sphere (0 : E) 1) (roundMetric (E := E) (n := n)) := by
  have hne : driftBaseline p r ≠ 0 := by
    intro hz
    let x : sphere (0 : E) 1 := ⟨p,by rw [mem_sphere_zero_iff_norm]; exact hp⟩
    have hx := congrArg (fun f : sphere (0 : E) 1 → ℝ => f x) hz
    exact (driftBaseline_pos p r x).ne' hx
  exact DFLC2WeakH1.contMDiff_two_exists_nonzero_completion_energy _ _
    ((driftBaseline_smooth (n := n) p r).of_le (by decide)) hne

end DFLDriftBaseline
