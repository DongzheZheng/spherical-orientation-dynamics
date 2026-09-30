import continuation.TiltStrictConcavity
import continuation.RoundSphereGroundSymmetry

/-! Antipodal symmetry and ordering of the actual full-domain minimum.
The proof transports a derived smooth minimizer by the genuine sphere
isometry and uses the original global Rayleigh bound. -/

noncomputable section
open Bundle Manifold MeasureTheory Set Filter Metric Module
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

namespace DFLSphere
private local instance (k : ℕ) : MeasurableSpace (RoundSphere k) := borel (RoundSphere k)
private local instance (k : ℕ) : BorelSpace (RoundSphere k) := ⟨rfl⟩
private local instance (k : ℕ) : IsFiniteMeasure (roundVolume k) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (roundSphereMetric k)

/-- Testing a genuine classical eigenfunction against itself gives its
actual full-domain energy, with no normalization assumption. -/
theorem round_smooth_classical_eigen_energy (k : ℕ) (V : RoundSphere k → ℝ)
    (hV : Continuous V) (lam : ℝ) (s : SmoothScalar (roundSphereMetric k))
    (heig : ∀ x, -ΔG (roundSphereMetric k) s.toContMDiffMap x +
      V x * s.toFun x = lam * s.toFun x) :
    roundPotentialEnergy k V (smoothToH1Compl (roundSphereMetric k) s) =
      lam * ‖smoothToLp (roundSphereMetric k) s‖ ^ 2 := by
  have hsI : Integrable (fun x => s.toFun x ^ 2) (roundVolume k) :=
    (s.smooth.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hVI : Integrable (fun x => V x * s.toFun x ^ 2) (roundVolume k) :=
    (hV.mul (s.smooth.continuous.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmass : ‖smoothToLp (roundSphereMetric k) s‖ ^ 2 =
      ∫ x, s.toFun x ^ 2 ∂roundVolume k := by
    have hh : ‖smoothToLp (roundSphereMetric k) s‖ ^ 2 =
        ∫ x, s.toFun x * s.toFun x ∂roundVolume k := s.norm_smoothToLp_sq
    rw [hh]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  have hp : (∫ x, V x *
      (H1ComplToLp (roundSphereMetric k) (smoothToH1Compl (roundSphereMetric k) s) x) ^ 2
      ∂roundVolume k) = ∫ x, V x * s.toFun x ^ 2 ∂roundVolume k := by
    rw [H1ComplToLp_smoothToH1Compl]
    apply integral_congr_ae
    filter_upwards [s.memLp_two.coeFn_toLp] with x hx
    have hxs : smoothToLp (roundSphereMetric k) s x = s.toFun x := hx
    rw [hxs]
  have hlap : (∫ x, s.toFun x * ΔG (roundSphereMetric k) s.toContMDiffMap x
      ∂roundVolume k) = (∫ x, V x * s.toFun x ^ 2 ∂roundVolume k) -
        lam * ∫ x, s.toFun x ^ 2 ∂roundVolume k := by
    calc
      _ = ∫ x, V x * s.toFun x ^ 2 - lam * s.toFun x ^ 2 ∂roundVolume k := by
        apply integral_congr_ae
        filter_upwards [] with x
        have hx := congrArg (fun q : ℝ => q * s.toFun x) (heig x)
        nlinarith only [hx]
      _ = _ := by rw [integral_sub hVI (hsI.const_mul lam), integral_const_mul]
  have hg : (∫ x, (roundSphereMetric k).inner x
      (gradFun (roundSphereMetric k) s.toFun x) (gradFun (roundSphereMetric k) s.toFun x)
      ∂roundVolume k) = -∫ x, s.toFun x *
        ΔG (roundSphereMetric k) s.toContMDiffMap x ∂roundVolume k :=
    green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
      (roundSphereMetric k) s.smooth s.smooth (HasCompactSupport.of_compactSpace _)
  unfold roundPotentialEnergy
  rw [h1_smooth_energy, hp, hg, hlap, hmass]
  ring

private def antipodalSmooth (k : ℕ) (s : SmoothScalar (roundSphereMetric k)) :
    SmoothScalar (roundSphereMetric k) :=
  ⟨fun x => s.toFun (sphereDiffeo (n := k + 2) (LinearIsometryEquiv.neg ℝ) x),
    s.smooth.comp (sphereDiffeo (n := k + 2) (LinearIsometryEquiv.neg ℝ)).contMDiff⟩

private theorem antipodal_coordinate (k : ℕ) (x : RoundSphere k) :
    (roundCoordinate k).toFun
      (sphereDiffeo (n := k + 2) (LinearIsometryEquiv.neg ℝ) x) =
      -(roundCoordinate k).toFun x := by
  change ⟪EuclideanSpace.single (0 : Fin (k + 3)) (1 : ℝ),
    (sphereDiffeo (n := k + 2) (LinearIsometryEquiv.neg ℝ) x : RoundAmbient k)⟫_ℝ =
      -⟪EuclideanSpace.single (0 : Fin (k + 3)) (1 : ℝ), (x : RoundAmbient k)⟫_ℝ
  rw [sphereDiffeo_coe]
  simp only [LinearIsometryEquiv.coe_neg, inner_neg_right]

private theorem antipodal_tilt (k : ℕ) (lam0 r a : ℝ) (x : RoundSphere k) :
    roundTiltPotential k lam0 r a
      (sphereDiffeo (n := k + 2) (LinearIsometryEquiv.neg ℝ) x) =
      roundTiltPotential k lam0 r (-a) x := by
  unfold roundTiltPotential
  rw [antipodal_coordinate]
  ring

private theorem antipodal_norm_pos (k : ℕ) (s : SmoothScalar (roundSphereMetric k))
    (hs : ‖smoothToLp (roundSphereMetric k) s‖ = 1) :
    0 < ‖smoothToLp (roundSphereMetric k) (antipodalSmooth k s)‖ := by
  apply norm_pos_iff.mpr
  intro hzero
  have hz : antipodalSmooth k s = 0 :=
    smoothToLp_injective (roundSphereMetric k)
      (hzero.trans ((smoothToLp (roundSphereMetric k)).map_zero).symm)
  have hs0 : s = 0 := by
    ext y
    change s.toFun y = 0
    let Φ := sphereDiffeo (n := k + 2)
      (LinearIsometryEquiv.neg ℝ : RoundAmbient k ≃ₗᵢ[ℝ] RoundAmbient k)
    have he := congrArg (fun f : SmoothScalar (roundSphereMetric k) => f.toFun (Φ.symm y)) hz
    change s.toFun (Φ (Φ.symm y)) = 0 at he
    simpa only [Φ.apply_symm_apply] using he
  rw [hs0, (smoothToLp (roundSphereMetric k)).map_zero, norm_zero] at hs
  norm_num at hs

private theorem roundTiltMinimum_reflected_le (k : ℕ) (lam0 r a : ℝ) :
    roundTiltMinimum k lam0 r (-a) ≤ roundTiltMinimum k lam0 r a := by
  obtain ⟨s, hn, _, _, heig⟩ := roundTiltMinimum_classical_minimizer k lam0 r a
  let f := antipodalSmooth k s
  have he : ∀ x, -ΔG (roundSphereMetric k) f.toContMDiffMap x +
      roundTiltPotential k lam0 r (-a) x * f.toFun x =
        roundTiltMinimum k lam0 r a * f.toFun x := by
    intro x
    have hmap : f.toContMDiffMap = DFLGroundSymmetry.orthogonalPullback
        (LinearIsometryEquiv.neg ℝ) s.toContMDiffMap := by
      ext y
      rfl
    have hL := DFLGroundSymmetry.orthogonalPullback_laplacian
      (n := k + 2) (LinearIsometryEquiv.neg ℝ) s.toContMDiffMap x
    change ΔG (roundSphereMetric k)
      (DFLGroundSymmetry.orthogonalPullback (LinearIsometryEquiv.neg ℝ) s.toContMDiffMap) x =
      ΔG (roundSphereMetric k) s.toContMDiffMap
        (sphereDiffeo (n := k + 2) (LinearIsometryEquiv.neg ℝ) x) at hL
    rw [hmap, hL]
    change -ΔG (roundSphereMetric k) s.toContMDiffMap
      (sphereDiffeo (n := k + 2) (LinearIsometryEquiv.neg ℝ) x) +
        roundTiltPotential k lam0 r (-a) x * s.toFun
          (sphereDiffeo (n := k + 2) (LinearIsometryEquiv.neg ℝ) x) =
      roundTiltMinimum k lam0 r a * s.toFun
        (sphereDiffeo (n := k + 2) (LinearIsometryEquiv.neg ℝ) x)
    rw [← antipodal_tilt]
    exact heig _
  have hE := round_smooth_classical_eigen_energy k (roundTiltPotential k lam0 r (-a))
    (roundTiltPotential_continuous k lam0 r (-a)) (roundTiltMinimum k lam0 r a) f he
  obtain ⟨_, _, _, hmin⟩ := roundPotentialMinimum_minimizer k
    (roundTiltPotential k lam0 r (-a)) (roundTiltPotential_continuous k lam0 r (-a))
  have hb := hmin (smoothToH1Compl (roundSphereMetric k) f)
  rw [H1ComplToLp_smoothToH1Compl, hE] at hb
  have hpos := sq_pos_of_pos (antipodal_norm_pos k s hn)
  change roundTiltMinimum k lam0 r (-a) * ‖smoothToLp (roundSphereMetric k) f‖ ^ 2 ≤
    roundTiltMinimum k lam0 r a * ‖smoothToLp (roundSphereMetric k) f‖ ^ 2 at hb
  change 0 < ‖smoothToLp (roundSphereMetric k) f‖ ^ 2 at hpos
  nlinarith

/-- The true full-H¹ minimum is even in its tilt parameter. This is proved
by genuine antipodal Laplacian naturality and the actual variational bound. -/
theorem roundTiltMinimum_even (k : ℕ) (lam0 r a : ℝ) :
    roundTiltMinimum k lam0 r (-a) = roundTiltMinimum k lam0 r a := by
  apply le_antisymm (roundTiltMinimum_reflected_le k lam0 r a)
  simpa only [neg_neg] using roundTiltMinimum_reflected_le k lam0 r (-a)

/-- A nonzero field makes the actual tilt minimum strictly decreasing on
nonnegative tilt strengths, including the endpoint at zero. -/
theorem roundTiltMinimum_strictAnti_nonnegative (k : ℕ) (lam0 r a b : ℝ)
    (hr : r ≠ 0) (ha : 0 ≤ a) (hab : a < b) :
    roundTiltMinimum k lam0 r b < roundTiltMinimum k lam0 r a := by
  have hb : 0 < b := lt_of_le_of_lt ha hab
  let z := (a + b) / (2 * b)
  have hz : 0 < z := div_pos (by linarith) (by positivity)
  have hz1 : z < 1 := (div_lt_one (by positivity : 0 < 2 * b)).mpr (by linarith)
  have hmix : z * b + (1 - z) * (-b) = a := by
    dsimp [z]
    field_simp
    ring
  have h := roundTiltMinimum_strict_concave_bound k lam0 r b (-b) z hr
    (by linarith) hz hz1
  rw [hmix, roundTiltMinimum_even] at h
  nlinarith

/-- The manuscript's radial and transverse half-density tilts have the
strict ordering on the actual common full auxiliary-sphere form domain. -/
theorem roundTiltMinimum_radial_transverse_order (d : ℕ) (hd : 2 ≤ d)
    (r : ℝ) (hr : 0 < r) :
    roundTiltMinimum d (d : ℝ) r ((d : ℝ) / 2) <
      roundTiltMinimum d (d : ℝ) r (((d : ℝ) - 2) / 2) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact roundTiltMinimum_strictAnti_nonnegative d (d : ℝ) r _ _ (ne_of_gt hr)
    (by linarith) (by linarith)

end DFLSphere
