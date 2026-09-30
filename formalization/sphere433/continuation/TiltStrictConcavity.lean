import continuation.PotentialRayleighStationarity
import continuation.RoundSphereGroundDomain
import continuation.RoundSphereLatitudeOperator

/-! Strict concavity of the true full-domain tilt minimum. Equality would
make a genuine smooth minimizer a common eigenfunction for two different
linear tilts. Its nonzero open set would make latitude locally constant,
contradicting the actual coordinate gradient and Laplacian identities. -/

noncomputable section
open Bundle Manifold MeasureTheory Set Filter Metric Module
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Analysis.Laplacian DifferentialGeometry.Integral.Measure

namespace DFLSphere

private local instance (k : ℕ) : MeasurableSpace (RoundSphere k) := borel (RoundSphere k)
private local instance (k : ℕ) : BorelSpace (RoundSphere k) := ⟨rfl⟩
private local instance (k : ℕ) : IsFiniteMeasure (roundVolume k) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (roundSphereMetric k)

/-- Attainment of the actual full-domain Rayleigh lower bound implies the
weak Schrödinger equation for every test in that domain. -/
theorem round_rayleigh_equality_weak (k : ℕ) (V : RoundSphere k → ℝ)
    (hV : Continuous V) (lam : ℝ) (U : H1Compl (roundSphereMetric k))
    (heq : roundPotentialEnergy k V U = lam * ‖H1ComplToLp (roundSphereMetric k) U‖ ^ 2)
    (hmin : ∀ W : H1Compl (roundSphereMetric k),
      lam * ‖H1ComplToLp (roundSphereMetric k) W‖ ^ 2 ≤ roundPotentialEnergy k V W) :
    IsRoundWeakPotentialEigenstate k V lam U := by
  let J := H1ComplToLp (roundSphereMetric k)
  have htop : MemLp V ∞ (roundVolume k) :=
    hV.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let P := boundedPotentialMultiplication V htop
  have hform (W Z : H1Compl (roundSphereMetric k)) :
      potentialForm J P W Z = ⟪W, Z⟫_ℝ - ⟪J W, J Z⟫_ℝ +
        ∫ x, V x * J W x * J Z x ∂roundVolume k := by
    unfold potentialForm
    change _ + ⟪boundedPotentialMultiplication V htop (J W), J Z⟫_ℝ = _
    rw [boundedPotentialMultiplication_inner]
  have hdiag (W : H1Compl (roundSphereMetric k)) :
      potentialForm J P W W = roundPotentialEnergy k V W := by
    rw [hform, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    unfold roundPotentialEnergy
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have he := potential_form_rayleigh_equality_stationary J P
    (boundedPotentialMultiplication_symmetric V htop) lam
    (fun W => by rw [hdiag]; exact hmin W) U (by rw [hdiag]; exact heq)
  intro W
  have hh := he W
  rw [hform] at hh
  exact hh

/-- Smoothness and the pointwise equation follow from an attained Rayleigh
bound; no separate regularity or eigenstate premise is needed. -/
theorem round_smooth_rayleigh_equality_pointwise (k : ℕ)
    (V : C^∞⟮𝓡 (k + 2), RoundSphere k; ℝ⟯) (lam : ℝ)
    (s : SmoothScalar (roundSphereMetric k))
    (heq : roundPotentialEnergy k V (smoothToH1Compl (roundSphereMetric k) s) =
      lam * ‖smoothToLp (roundSphereMetric k) s‖ ^ 2)
    (hmin : ∀ W : H1Compl (roundSphereMetric k),
      lam * ‖H1ComplToLp (roundSphereMetric k) W‖ ^ 2 ≤ roundPotentialEnergy k V W) :
    ∀ x, -ΔG (roundSphereMetric k) s.toContMDiffMap x + V x * s.toFun x =
      lam * s.toFun x := by
  have hw := round_rayleigh_equality_weak k V V.contMDiff.continuous lam
    (smoothToH1Compl (roundSphereMetric k) s)
    (by rw [H1ComplToLp_smoothToH1Compl]; exact heq) hmin
  obtain ⟨f, hf, he⟩ := round_weak_smooth_potential_eigen_pointwise k V lam _ hw
  have hsf : s = f := by
    apply smoothToLp_injective (roundSphereMetric k)
    have hJ := congrArg (H1ComplToLp (roundSphereMetric k)) hf
    simpa only [H1ComplToLp_smoothToH1Compl] using hJ
  simpa only [hsf] using he

/-- The actual tilt infimum is attained by a normalized smooth classical
state. Both existence and its full-domain minimizing property are derived. -/
theorem roundTiltMinimum_classical_minimizer (k : ℕ) (lam0 r a : ℝ) :
    ∃ s : SmoothScalar (roundSphereMetric k),
      ‖smoothToLp (roundSphereMetric k) s‖ = 1 ∧
      roundPotentialEnergy k (roundTiltPotential k lam0 r a)
        (smoothToH1Compl (roundSphereMetric k) s) = roundTiltMinimum k lam0 r a ∧
      (∀ W : H1Compl (roundSphereMetric k),
        roundTiltMinimum k lam0 r a * ‖H1ComplToLp (roundSphereMetric k) W‖ ^ 2 ≤
          roundPotentialEnergy k (roundTiltPotential k lam0 r a) W) ∧
      ∀ x, -ΔG (roundSphereMetric k) s.toContMDiffMap x +
        roundTiltPotential k lam0 r a x * s.toFun x =
          roundTiltMinimum k lam0 r a * s.toFun x := by
  obtain ⟨U, hn, he, hmin⟩ := roundPotentialMinimum_minimizer k
    (roundTiltPotential k lam0 r a) (roundTiltPotential_continuous k lam0 r a)
  have hw := round_rayleigh_equality_weak k (roundTiltPotential k lam0 r a)
    (roundTiltPotential_continuous k lam0 r a) (roundTiltMinimum k lam0 r a) U
    (by rw [hn, one_pow, mul_one]; exact he) hmin
  obtain ⟨s, hs, hp⟩ := round_weak_smooth_potential_eigen_pointwise k
    (roundTiltSmoothPotential k lam0 r a) (roundTiltMinimum k lam0 r a) U hw
  rw [hs, H1ComplToLp_smoothToH1Compl] at hn
  rw [hs] at he
  exact ⟨s, hn, he, hmin, hp⟩

private theorem roundCoordinate_not_locally_constant (k : ℕ) (x : RoundSphere k)
    (c : ℝ) (heq : (roundCoordinate k).toFun =ᶠ[𝓝 x] fun _ => c) : False := by
  let g := roundSphereMetric k
  let t := (roundCoordinate k).toContMDiffMap
  have hg : gradientFun g (t : RoundSphere k → ℝ) x = 0 := by
    apply gradientFun_eq_zero_of_mfderiv_eq_zero
    change mfderiv (𝓡 (k + 2)) 𝓘(ℝ, ℝ) (roundCoordinate k).toFun x = 0
    rw [heq.mfderiv_eq]
    exact mfderiv_const
  have hnorm := DFLLatitudeOperator.latitude_gradient_norm_sq
    (n := k + 2) (EuclideanSpace.single (0 : Fin (k + 3)) (1 : ℝ)) (by simp) x
  change g.inner x (gradientFun g t x) (gradientFun g t x) =
    1 - (roundCoordinate k).toFun x ^ 2 at hnorm
  rw [hg] at hnorm
  simp only [map_zero] at hnorm
  have hl := laplacian_congr_of_eventuallyEq (LeviCivita g) g
    t.contMDiff.contMDiffAt contMDiffAt_const heq
  rw [laplacian_const, laplacian_levi_eq g t.contMDiff] at hl
  change ΔG g t x = 0 at hl
  have hc := roundCoordinate_eigen k x
  change ΔG g t x = -(k + 2 : ℝ) * (roundCoordinate k).toFun x at hc
  rw [hl] at hc
  have hn : (k + 2 : ℝ) ≠ 0 := by positivity
  have ht : (roundCoordinate k).toFun x = 0 := by
    exact (mul_eq_zero.mp hc.symm).resolve_left (neg_ne_zero.mpr hn)
  rw [ht] at hnorm
  norm_num at hnorm

private theorem round_tilt_residual_impossible (k : ℕ)
    (s : SmoothScalar (roundSphereMetric k)) (hs : ‖smoothToLp (roundSphereMetric k) s‖ = 1)
    (A B : ℝ) (hA : A ≠ 0)
    (hres : ∀ x, (A * (roundCoordinate k).toFun x - B) * s.toFun x = 0) : False := by
  have hnz : ∃ x, s.toFun x ≠ 0 := by
    by_contra h
    push Not at h
    have hs0 : s = 0 := by ext x; exact h x
    rw [hs0, (smoothToLp (roundSphereMetric k)).map_zero, norm_zero] at hs
    norm_num at hs
  obtain ⟨x, hx⟩ := hnz
  have hopen : IsOpen {y : RoundSphere k | s.toFun y ≠ 0} :=
    isOpen_ne.preimage s.smooth.continuous
  have ht : (roundCoordinate k).toFun =ᶠ[𝓝 x] fun _ => B / A := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    have he := (mul_eq_zero.mp (hres y)).resolve_right hy
    apply (eq_div_iff hA).mpr
    linarith
  exact roundCoordinate_not_locally_constant k x (B / A) ht

/-- Strict concavity is proved for the actual minimum at every nonzero
field. Its equality case is ruled out by the true sphere geometry. -/
theorem roundTiltMinimum_strict_concave_bound (k : ℕ) (lam0 r a b z : ℝ)
    (hr : r ≠ 0) (hab : a ≠ b) (hz : 0 < z) (hz1 : z < 1) :
    z * roundTiltMinimum k lam0 r a + (1 - z) * roundTiltMinimum k lam0 r b <
      roundTiltMinimum k lam0 r (z * a + (1 - z) * b) := by
  let m := z * a + (1 - z) * b
  obtain ⟨s, hn, he, _, _⟩ := roundTiltMinimum_classical_minimizer k lam0 r m
  let U := smoothToH1Compl (roundSphereMetric k) s
  obtain ⟨_, _, _, ha⟩ := roundPotentialMinimum_minimizer k
    (roundTiltPotential k lam0 r a) (roundTiltPotential_continuous k lam0 r a)
  obtain ⟨_, _, _, hb⟩ := roundPotentialMinimum_minimizer k
    (roundTiltPotential k lam0 r b) (roundTiltPotential_continuous k lam0 r b)
  have hUa := ha U
  have hUb := hb U
  change roundTiltMinimum k lam0 r a * ‖H1ComplToLp (roundSphereMetric k) U‖ ^ 2 ≤
    roundPotentialEnergy k (roundTiltPotential k lam0 r a) U at hUa
  change roundTiltMinimum k lam0 r b * ‖H1ComplToLp (roundSphereMetric k) U‖ ^ 2 ≤
    roundPotentialEnergy k (roundTiltPotential k lam0 r b) U at hUb
  have hUn : ‖H1ComplToLp (roundSphereMetric k) U‖ = 1 := by
    rw [H1ComplToLp_smoothToH1Compl]; exact hn
  rw [hUn, one_pow, mul_one] at hUa hUb
  have haff : roundPotentialEnergy k (roundTiltPotential k lam0 r m) U =
      z * roundPotentialEnergy k (roundTiltPotential k lam0 r a) U +
      (1 - z) * roundPotentialEnergy k (roundTiltPotential k lam0 r b) U := by
    have hp : z • roundTiltContinuousPotential k lam0 r a +
        (1 - z) • roundTiltContinuousPotential k lam0 r b =
        roundTiltContinuousPotential k lam0 r m := by
      ext x
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
      dsimp [roundTiltContinuousPotential, roundTiltPotential, m]
      ring
    have hh := roundPotentialEnergy_affine k
      (roundTiltContinuousPotential k lam0 r a) (roundTiltContinuousPotential k lam0 r b) z U
    rw [hp] at hh
    exact hh
  change roundPotentialEnergy k (roundTiltPotential k lam0 r m) U =
    roundTiltMinimum k lam0 r m at he
  by_contra hstrict
  have heqa : roundPotentialEnergy k (roundTiltPotential k lam0 r a) U =
      roundTiltMinimum k lam0 r a := by
    rw [haff] at he
    have hh : roundTiltMinimum k lam0 r m ≤
        z * roundTiltMinimum k lam0 r a + (1 - z) * roundTiltMinimum k lam0 r b :=
      le_of_not_gt hstrict
    nlinarith
  have heqb : roundPotentialEnergy k (roundTiltPotential k lam0 r b) U =
      roundTiltMinimum k lam0 r b := by
    rw [haff] at he
    have hh : roundTiltMinimum k lam0 r m ≤
        z * roundTiltMinimum k lam0 r a + (1 - z) * roundTiltMinimum k lam0 r b :=
      le_of_not_gt hstrict
    nlinarith
  have hpa := round_smooth_rayleigh_equality_pointwise k (roundTiltSmoothPotential k lam0 r a)
    (roundTiltMinimum k lam0 r a) s (by rw [hn, one_pow, mul_one]; exact heqa) ha
  have hpb := round_smooth_rayleigh_equality_pointwise k (roundTiltSmoothPotential k lam0 r b)
    (roundTiltMinimum k lam0 r b) s (by rw [hn, one_pow, mul_one]; exact heqb) hb
  apply round_tilt_residual_impossible k s hn ((a - b) * r)
    (roundTiltMinimum k lam0 r b - roundTiltMinimum k lam0 r a)
    (mul_ne_zero (sub_ne_zero.mpr hab) hr)
  intro x
  have hxa := hpa x
  have hxb := hpb x
  change -ΔG (roundSphereMetric k) s.toContMDiffMap x +
    (lam0 + r ^ 2 / 4 * (1 - (roundCoordinate k).toFun x ^ 2) -
      a * r * (roundCoordinate k).toFun x) * s.toFun x =
      roundTiltMinimum k lam0 r a * s.toFun x at hxa
  change -ΔG (roundSphereMetric k) s.toContMDiffMap x +
    (lam0 + r ^ 2 / 4 * (1 - (roundCoordinate k).toFun x ^ 2) -
      b * r * (roundCoordinate k).toFun x) * s.toFun x =
      roundTiltMinimum k lam0 r b * s.toFun x at hxb
  nlinarith

/-- The genuine full-domain tilt minimum is strictly concave on all real
parameters when the field is nonzero. -/
theorem roundTiltMinimum_strictConcave (k : ℕ) (lam0 r : ℝ) (hr : r ≠ 0) :
    StrictConcaveOn ℝ Set.univ (roundTiltMinimum k lam0 r) := by
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ hab s t hs ht hsum
  have hteq : t = 1 - s := by linarith
  rw [hteq]
  simpa only [smul_eq_mul] using
    roundTiltMinimum_strict_concave_bound k lam0 r a b s hr hab hs (by linarith)

end DFLSphere
