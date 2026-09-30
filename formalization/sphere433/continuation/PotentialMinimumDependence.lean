import DFLSphere433.RoundSpherePotentialGround
import DFLSphere433.WeightedSpherePoincare
import Mathlib.Analysis.Convex.Function

/-! Dependence of the actual full-H¹ variational minimum on a continuous
real potential. No branch, minimum, positivity, or eigenvector is assumed. -/

noncomputable section
open Bundle Manifold MeasureTheory Set Filter Metric
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DFLSphere
open DifferentialGeometry DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Measure

private local instance (k : ℕ) : MeasurableSpace (RoundSphere k) := borel (RoundSphere k)
private local instance (k : ℕ) : BorelSpace (RoundSphere k) := ⟨rfl⟩
private local instance (k : ℕ) : IsFiniteMeasure (roundVolume k) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (roundSphereMetric k)

/-- The normalized Rayleigh values on the original full form domain. -/
def roundPotentialRayleighValues (k : ℕ) (V : RoundSphere k → ℝ) : Set ℝ :=
  {q | ∃ U : H1Compl (roundSphereMetric k),
    ‖H1ComplToLp (roundSphereMetric k) U‖ = 1 ∧ q = roundPotentialEnergy k V U}

def roundPotentialMinimum (k : ℕ) (V : RoundSphere k → ℝ) : ℝ :=
  sInf (roundPotentialRayleighValues k V)

/-- Existence and the global Rayleigh bound are derived from the actual
compact form operator, rather than supplied as spectral assumptions. -/
theorem roundPotentialMinimum_minimizer (k : ℕ) (V : RoundSphere k → ℝ)
    (hV : Continuous V) :
    ∃ U : H1Compl (roundSphereMetric k),
      ‖H1ComplToLp (roundSphereMetric k) U‖ = 1 ∧
      roundPotentialEnergy k V U = roundPotentialMinimum k V ∧
      ∀ W : H1Compl (roundSphereMetric k),
        roundPotentialMinimum k V * ‖H1ComplToLp (roundSphereMetric k) W‖ ^ 2 ≤
          roundPotentialEnergy k V W := by
  obtain ⟨lam, U, hn, he, hmin, _⟩ := round_potential_ground_exists k V hV
  have hleast : lam ∈ lowerBounds (roundPotentialRayleighValues k V) := by
    rintro q ⟨W, hw, rfl⟩
    simpa only [hw, one_pow, mul_one] using hmin W
  have hmem : lam ∈ roundPotentialRayleighValues k V := ⟨U, hn, he.symm⟩
  have hvalue : roundPotentialMinimum k V = lam :=
    le_antisymm (csInf_le ⟨_, hleast⟩ hmem) (le_csInf ⟨_, hmem⟩ hleast)
  exact ⟨U, hn, he.trans hvalue.symm, hvalue.symm ▸ hmin⟩

private theorem potential_mass_sq (k : ℕ) (U : H1Compl (roundSphereMetric k)) :
    ‖H1ComplToLp (roundSphereMetric k) U‖ ^ 2 =
      ∫ x, (H1ComplToLp (roundSphereMetric k) U x) ^ 2 ∂roundVolume k := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Real.inner_apply, pow_two]

private theorem potential_mass_integrable (k : ℕ) (U : H1Compl (roundSphereMetric k)) :
    Integrable (fun x => (H1ComplToLp (roundSphereMetric k) U x) ^ 2) (roundVolume k) := by
  have hf := Lp.memLp (H1ComplToLp (roundSphereMetric k) U)
  exact (hf.integrable_mul hf).congr (ae_of_all _ (fun x => by simp only [Pi.mul_apply, pow_two]))

private theorem continuous_potential_integrable (k : ℕ) (V : C(RoundSphere k, ℝ))
    (U : H1Compl (roundSphereMetric k)) :
    Integrable (fun x => V x * (H1ComplToLp (roundSphereMetric k) U x) ^ 2) (roundVolume k) :=
  (potential_mass_integrable k U).bdd_mul V.continuous.aestronglyMeasurable
    (ae_of_all _ (fun x => V.norm_coe_le_norm x))

theorem roundPotentialEnergy_mono (k : ℕ) (V W : C(RoundSphere k, ℝ))
    (hle : ∀ x, V x ≤ W x) (U : H1Compl (roundSphereMetric k)) :
    roundPotentialEnergy k V U ≤ roundPotentialEnergy k W U := by
  unfold roundPotentialEnergy
  have h := integral_mono (continuous_potential_integrable k V U)
    (continuous_potential_integrable k W U) (fun x =>
      mul_le_mul_of_nonneg_right (hle x) (sq_nonneg _))
  linarith

theorem roundPotentialMinimum_mono (k : ℕ) (V W : C(RoundSphere k, ℝ))
    (hle : ∀ x, V x ≤ W x) : roundPotentialMinimum k V ≤ roundPotentialMinimum k W := by
  obtain ⟨U, hn, he, _⟩ := roundPotentialMinimum_minimizer k W W.continuous
  obtain ⟨_, _, _, hmin⟩ := roundPotentialMinimum_minimizer k V V.continuous
  have h := hmin U
  rw [hn, one_pow, mul_one] at h
  exact h.trans ((roundPotentialEnergy_mono k V W hle U).trans_eq he)

theorem roundPotentialEnergy_shift (k : ℕ) (V : C(RoundSphere k, ℝ)) (c : ℝ)
    (U : H1Compl (roundSphereMetric k)) :
    roundPotentialEnergy k ⇑(V + ContinuousMap.const (RoundSphere k) c) U =
      roundPotentialEnergy k V U + c * ‖H1ComplToLp (roundSphereMetric k) U‖ ^ 2 := by
  have hi : (∫ x, (V + ContinuousMap.const (RoundSphere k) c) x *
      (H1ComplToLp (roundSphereMetric k) U x) ^ 2 ∂roundVolume k) =
      (∫ x, V x * (H1ComplToLp (roundSphereMetric k) U x) ^ 2 ∂roundVolume k) +
        c * ∫ x, (H1ComplToLp (roundSphereMetric k) U x) ^ 2 ∂roundVolume k := by
    calc
      _ = ∫ x, V x * (H1ComplToLp (roundSphereMetric k) U x) ^ 2 +
          c * (H1ComplToLp (roundSphereMetric k) U x) ^ 2 ∂roundVolume k := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
        ring
      _ = _ := by rw [integral_add (continuous_potential_integrable k V U)
        ((potential_mass_integrable k U).const_mul c), integral_const_mul]
  unfold roundPotentialEnergy
  rw [hi, potential_mass_sq]
  ring

theorem roundPotentialMinimum_shift (k : ℕ) (V : C(RoundSphere k, ℝ)) (c : ℝ) :
    roundPotentialMinimum k ⇑(V + ContinuousMap.const (RoundSphere k) c) =
      roundPotentialMinimum k V + c := by
  obtain ⟨U, hn, he, hmin⟩ := roundPotentialMinimum_minimizer k V V.continuous
  obtain ⟨W, hwn, hwe, hwmin⟩ := roundPotentialMinimum_minimizer k
    ⇑(V + ContinuousMap.const (RoundSphere k) c)
    (V + ContinuousMap.const (RoundSphere k) c).continuous
  have h1 := hwmin U
  have h2 := hmin W
  rw [roundPotentialEnergy_shift, hn, one_pow, mul_one, he, mul_one] at h1
  rw [hwn, one_pow, mul_one] at h2
  rw [roundPotentialEnergy_shift, hwn, one_pow, mul_one] at hwe
  linarith

/-- Uniform perturbation of the actual potential changes the lowest
variational value by at most the same amount. -/
theorem roundPotentialMinimum_lipschitz_bound (k : ℕ) (V W : C(RoundSphere k, ℝ))
    (C : ℝ) (hbound : ∀ x, |V x - W x| ≤ C) :
    |roundPotentialMinimum k V - roundPotentialMinimum k W| ≤ C := by
  have h1 := roundPotentialMinimum_mono k V (W + ContinuousMap.const (RoundSphere k) C)
    (fun x => by
      change V x ≤ W x + C
      have h := (abs_le.mp (hbound x)).2
      linarith)
  have h2 := roundPotentialMinimum_mono k W (V + ContinuousMap.const (RoundSphere k) C)
    (fun x => by
      change W x ≤ V x + C
      have h := (abs_le.mp (hbound x)).1
      linarith)
  rw [roundPotentialMinimum_shift] at h1 h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem roundPotentialMinimum_lipschitz (k : ℕ) :
    LipschitzWith 1 (fun V : C(RoundSphere k, ℝ) => roundPotentialMinimum k V) := by
  apply LipschitzWith.of_dist_le_mul
  intro V W
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  apply roundPotentialMinimum_lipschitz_bound
  intro x
  simpa only [Real.norm_eq_abs, ContinuousMap.sub_apply, dist_eq_norm] using
    (V - W).norm_coe_le_norm x

theorem roundPotentialMinimum_continuous (k : ℕ) :
    Continuous (fun V : C(RoundSphere k, ℝ) => roundPotentialMinimum k V) :=
  (roundPotentialMinimum_lipschitz k).continuous

/-- The same fixed-domain energy is affine in the actual potential. -/
theorem roundPotentialEnergy_affine (k : ℕ) (V W : C(RoundSphere k, ℝ)) (s : ℝ)
    (U : H1Compl (roundSphereMetric k)) :
    roundPotentialEnergy k ⇑(s • V + (1 - s) • W) U =
      s * roundPotentialEnergy k V U + (1 - s) * roundPotentialEnergy k W U := by
  have hi : (∫ x, (s • V + (1 - s) • W) x *
      (H1ComplToLp (roundSphereMetric k) U x) ^ 2 ∂roundVolume k) =
      s * (∫ x, V x * (H1ComplToLp (roundSphereMetric k) U x) ^ 2 ∂roundVolume k) +
      (1 - s) * (∫ x, W x * (H1ComplToLp (roundSphereMetric k) U x) ^ 2 ∂roundVolume k) := by
    calc
      _ = ∫ x, s * (V x * (H1ComplToLp (roundSphereMetric k) U x) ^ 2) +
          (1 - s) * (W x * (H1ComplToLp (roundSphereMetric k) U x) ^ 2) ∂roundVolume k := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
        ring
      _ = _ := by rw [integral_add ((continuous_potential_integrable k V U).const_mul s)
        ((continuous_potential_integrable k W U).const_mul (1 - s)),
        integral_const_mul, integral_const_mul]
  unfold roundPotentialEnergy
  rw [hi]
  ring

/-- Concavity follows from the actual global Rayleigh principle and
attainment on the full form domain. -/
theorem roundPotentialMinimum_concave_bound (k : ℕ) (V W : C(RoundSphere k, ℝ))
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    s * roundPotentialMinimum k V + (1 - s) * roundPotentialMinimum k W ≤
      roundPotentialMinimum k ⇑(s • V + (1 - s) • W) := by
  obtain ⟨U, hn, he, _⟩ := roundPotentialMinimum_minimizer k
    ⇑(s • V + (1 - s) • W) (s • V + (1 - s) • W).continuous
  obtain ⟨_, _, _, hV⟩ := roundPotentialMinimum_minimizer k V V.continuous
  obtain ⟨_, _, _, hW⟩ := roundPotentialMinimum_minimizer k W W.continuous
  have ha := hV U
  have hb := hW U
  rw [hn, one_pow, mul_one] at ha hb
  rw [roundPotentialEnergy_affine] at he
  calc
    _ ≤ s * roundPotentialEnergy k V U + (1 - s) * roundPotentialEnergy k W U :=
      add_le_add (mul_le_mul_of_nonneg_left ha hs)
        (mul_le_mul_of_nonneg_left hb (by linarith))
    _ = _ := he

def roundTiltContinuousPotential (k : ℕ) (lam0 r a : ℝ) : C(RoundSphere k, ℝ) :=
  ⟨roundTiltPotential k lam0 r a, roundTiltPotential_continuous k lam0 r a⟩

/-- The original tilt minimum, on the actual full auxiliary-sphere H¹ domain. -/
def roundTiltMinimum (k : ℕ) (lam0 r a : ℝ) : ℝ :=
  roundPotentialMinimum k (roundTiltPotential k lam0 r a)

theorem roundTiltMinimum_lipschitz_bound (k : ℕ) (lam0 r a b : ℝ) :
    |roundTiltMinimum k lam0 r a - roundTiltMinimum k lam0 r b| ≤ |r| * |a - b| := by
  apply roundPotentialMinimum_lipschitz_bound k
    (roundTiltContinuousPotential k lam0 r a) (roundTiltContinuousPotential k lam0 r b)
  intro x
  have he : roundTiltContinuousPotential k lam0 r a x -
      roundTiltContinuousPotential k lam0 r b x =
      -(a - b) * r * (roundCoordinate k).toFun x := by
    dsimp [roundTiltContinuousPotential, roundTiltPotential]
    ring
  rw [he, abs_mul, abs_mul, abs_neg]
  calc
    _ ≤ |a - b| * |r| * 1 :=
      mul_le_mul_of_nonneg_left (roundCoordinate_abs_le_one k x) (by positivity)
    _ = _ := by ring

theorem roundTiltMinimum_lipschitz (k : ℕ) (lam0 r : ℝ) :
    LipschitzWith (Real.toNNReal |r|) (roundTiltMinimum k lam0 r) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  change dist (roundTiltMinimum k lam0 r a) (roundTiltMinimum k lam0 r b) ≤
    (↑(Real.toNNReal |r|) : ℝ) * dist a b
  rw [Real.coe_toNNReal |r| (abs_nonneg r), Real.dist_eq, Real.dist_eq]
  exact roundTiltMinimum_lipschitz_bound k lam0 r a b

theorem roundTiltMinimum_continuous (k : ℕ) (lam0 r : ℝ) :
    Continuous (roundTiltMinimum k lam0 r) := (roundTiltMinimum_lipschitz k lam0 r).continuous

/-- Concavity of the original tilt minimum, derived on the full form domain. -/
theorem roundTiltMinimum_concave_bound (k : ℕ) (lam0 r a b s : ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    s * roundTiltMinimum k lam0 r a + (1 - s) * roundTiltMinimum k lam0 r b ≤
      roundTiltMinimum k lam0 r (s * a + (1 - s) * b) := by
  have hpot : s • roundTiltContinuousPotential k lam0 r a +
      (1 - s) • roundTiltContinuousPotential k lam0 r b =
      roundTiltContinuousPotential k lam0 r (s * a + (1 - s) * b) := by
    ext x
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
    dsimp [roundTiltContinuousPotential, roundTiltPotential]
    ring
  have h := roundPotentialMinimum_concave_bound k
    (roundTiltContinuousPotential k lam0 r a) (roundTiltContinuousPotential k lam0 r b) s hs hs1
  rw [hpot] at h
  exact h

theorem roundTiltMinimum_concave (k : ℕ) (lam0 r : ℝ) :
    ConcaveOn ℝ Set.univ (roundTiltMinimum k lam0 r) := by
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ s t hs ht hsum
  have hteq : t = 1 - s := by linarith
  rw [hteq]
  simpa only [smul_eq_mul] using roundTiltMinimum_concave_bound k lam0 r a b s hs (by linarith)

end DFLSphere
