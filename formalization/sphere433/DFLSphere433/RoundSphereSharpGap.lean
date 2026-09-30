import DFLSphere433.RoundSpherePoincare
import DFLSphere433.RoundSphereCoordinates

/-!
The exact zero-field gap of the original full round sphere is its
dimension. The minimization domain is the full H¹ form, and sharpness
is achieved by an actual ambient linear coordinate on that sphere.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Metric
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DFLSphere

open DifferentialGeometry
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open DFLSpectralCoordinates

instance (k : ℕ) : NeZero (k + 2) := ⟨by omega⟩

def roundCoordinate (k : ℕ) : SmoothScalar (roundSphereMetric k) :=
  ⟨innerCoordFun (E := RoundAmbient k) (n := k + 2) (EuclideanSpace.single 0 1),
    (innerCoordFun (E := RoundAmbient k) (n := k + 2)
      (EuclideanSpace.single 0 1)).contMDiff⟩

theorem roundCoordinate_eigen (k : ℕ) (x : RoundSphere k) :
    ΔG (roundSphereMetric k) (roundCoordinate k).toContMDiffMap x =
      -(k + 2 : ℝ) * (roundCoordinate k).toFun x := by
  have hmap : (roundCoordinate k).toContMDiffMap =
      innerCoordFun (E := RoundAmbient k) (n := k + 2) (EuclideanSpace.single 0 1) := by
    ext p
    rfl
  rw [hmap]
  change ΔG (roundMetric (E := RoundAmbient k) (n := k + 2))
    (innerCoordFun (E := RoundAmbient k) (n := k + 2) (EuclideanSpace.single 0 1)) x =
    -(k + 2 : ℝ) * ⟪EuclideanSpace.single 0 1, (x : RoundAmbient k)⟫_ℝ
  convert coordinate_laplacian (E := RoundAmbient k) (n := k + 2) x
    (EuclideanSpace.single 0 1) using 1
  norm_num

theorem roundCoordinate_mean_zero (k : ℕ) :
    (∫ x : RoundSphere k, (roundCoordinate k).toFun x
      ∂riemannianVolumeMeasure (𝓡 (k + 2)) (RoundSphere k) (roundSphereMetric k)) = 0 := by
  have hz := integral_divergence_eq_zero_of_compact (roundSphereMetric k)
    (gradG (roundSphereMetric k) (roundCoordinate k).toContMDiffMap)
  change (∫ x : RoundSphere k,
    ΔG (roundSphereMetric k) (roundCoordinate k).toContMDiffMap x
    ∂riemannianVolumeMeasure (𝓡 (k + 2)) (RoundSphere k) (roundSphereMetric k)) = 0 at hz
  simp_rw [roundCoordinate_eigen] at hz
  rw [integral_const_mul] at hz
  have hn : -(k + 2 : ℝ) ≠ 0 := neg_ne_zero.mpr (by positivity)
  exact (mul_eq_zero.mp hz).resolve_left hn

theorem roundCoordinate_nonzero (k : ℕ) : roundCoordinate k ≠ 0 := by
  let north : RoundSphere k := ⟨EuclideanSpace.single 0 1, by simp⟩
  intro h
  have hh := congrArg (fun f : SmoothScalar (roundSphereMetric k) => f.toFun north) h
  norm_num [roundCoordinate, north, innerCoordFun, EuclideanSpace.inner_single_left] at hh

theorem roundCoordinate_L2_norm_pos (k : ℕ) :
    0 < ‖smoothToLp (roundSphereMetric k) (roundCoordinate k)‖ := by
  apply norm_pos_iff.mpr
  intro h
  apply roundCoordinate_nonzero k
  exact smoothToLp_injective (roundSphereMetric k)
    (h.trans ((smoothToLp (roundSphereMetric k)).map_zero).symm)

theorem roundCoordinate_energy_exact (k : ℕ) :
    ‖smoothToH1Compl (roundSphereMetric k) (roundCoordinate k)‖ ^ 2 -
      ‖H1ComplToLp (roundSphereMetric k)
        (smoothToH1Compl (roundSphereMetric k) (roundCoordinate k))‖ ^ 2 =
      (k + 2 : ℝ) * ‖smoothToLp (roundSphereMetric k) (roundCoordinate k)‖ ^ 2 := by
  let f := roundCoordinate k
  have hg : (∫ x : RoundSphere k, (roundSphereMetric k).inner x
      (gradFun (roundSphereMetric k) f.toFun x) (gradFun (roundSphereMetric k) f.toFun x)
        ∂riemannianVolumeMeasure (𝓡 (k + 2)) (RoundSphere k) (roundSphereMetric k)) =
      -∫ x : RoundSphere k, f.toFun x * ΔG (roundSphereMetric k) f.toContMDiffMap x
        ∂riemannianVolumeMeasure (𝓡 (k + 2)) (RoundSphere k) (roundSphereMetric k) :=
    green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
      (roundSphereMetric k) f.smooth f.smooth (HasCompactSupport.of_compactSpace _)
  have hn : ‖smoothToLp (roundSphereMetric k) f‖ ^ 2 =
      ∫ x : RoundSphere k, f.toFun x * f.toFun x
        ∂riemannianVolumeMeasure (𝓡 (k + 2)) (RoundSphere k) (roundSphereMetric k) :=
    f.norm_smoothToLp_sq
  rw [h1_smooth_energy, hg, hn]
  have he : (fun x : RoundSphere k => f.toFun x * ΔG (roundSphereMetric k) f.toContMDiffMap x) =
      (fun x => -(k + 2 : ℝ) * (f.toFun x * f.toFun x)) := by
    funext x
    rw [roundCoordinate_eigen]
    ring
  rw [he, integral_const_mul]
  ring

def roundH1Rayleigh (k : ℕ) (u : H1Compl (roundSphereMetric k)) : ℝ :=
  (‖u‖ ^ 2 - ‖H1ComplToLp (roundSphereMetric k) u‖ ^ 2) /
    ‖H1ComplToLp (roundSphereMetric k) u‖ ^ 2

def roundH1RayleighValues (k : ℕ) : Set ℝ :=
  {q | ∃ u : H1Compl (roundSphereMetric k),
    (∫ x : RoundSphere k, (H1ComplToLp (roundSphereMetric k) u) x
      ∂riemannianVolumeMeasure (𝓡 (k + 2)) (RoundSphere k) (roundSphereMetric k)) = 0 ∧
    0 < ‖H1ComplToLp (roundSphereMetric k) u‖ ∧ q = roundH1Rayleigh k u}

def roundH1Gap (k : ℕ) : ℝ := sInf (roundH1RayleighValues k)

theorem roundH1Rayleigh_lower (k : ℕ) (u : H1Compl (roundSphereMetric k))
    (hmean : (∫ x : RoundSphere k, (H1ComplToLp (roundSphereMetric k) u) x
      ∂riemannianVolumeMeasure (𝓡 (k + 2)) (RoundSphere k) (roundSphereMetric k)) = 0)
    (hn : 0 < ‖H1ComplToLp (roundSphereMetric k) u‖) :
    (k + 2 : ℝ) ≤ roundH1Rayleigh k u := by
  apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
  exact roundSphere_h1_poincare k u hmean

theorem roundCoordinate_Rayleigh (k : ℕ) :
    roundH1Rayleigh k (smoothToH1Compl (roundSphereMetric k) (roundCoordinate k)) = (k + 2 : ℝ) := by
  unfold roundH1Rayleigh
  rw [roundCoordinate_energy_exact, H1ComplToLp_smoothToH1Compl]
  exact mul_div_cancel_right₀ _ (pow_ne_zero 2 (ne_of_gt (roundCoordinate_L2_norm_pos k)))

theorem roundDimension_mem_RayleighValues (k : ℕ) :
    (k + 2 : ℝ) ∈ roundH1RayleighValues k := by
  refine ⟨smoothToH1Compl (roundSphereMetric k) (roundCoordinate k), ?_, ?_, ?_⟩
  · rw [H1ComplToLp_smoothToH1Compl]
    exact (integral_congr_ae (MemLp.coeFn_toLp (roundCoordinate k).memLp_two)).trans
      (roundCoordinate_mean_zero k)
  · rw [H1ComplToLp_smoothToH1Compl]
    exact roundCoordinate_L2_norm_pos k
  · exact (roundCoordinate_Rayleigh k).symm

/-- Exact global zero-field gap, including its full H¹ minimization
domain and an actual coordinate-function minimizer. -/
theorem roundH1Gap_eq_dimension (k : ℕ) : roundH1Gap k = (k + 2 : ℝ) := by
  have hlower : (k + 2 : ℝ) ∈ lowerBounds (roundH1RayleighValues k) := by
    rintro q ⟨u, hmean, hn, rfl⟩
    exact roundH1Rayleigh_lower k u hmean hn
  have hne : (roundH1RayleighValues k).Nonempty := ⟨_, roundDimension_mem_RayleighValues k⟩
  unfold roundH1Gap
  exact le_antisymm (csInf_le ⟨_, hlower⟩ (roundDimension_mem_RayleighValues k))
    (le_csInf hne hlower)

end DFLSphere

#print axioms DFLSphere.roundCoordinate_eigen
#print axioms DFLSphere.roundCoordinate_energy_exact
#print axioms DFLSphere.roundH1Gap_eq_dimension
