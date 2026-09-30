import DFLSphere433.CompactFormGround
import DFLSphere433.RoundSphereSharpGap
import DFLSphere433.WeakH1Completion

/-! Lowest Rayleigh value for an actual continuous real potential on the
true round sphere, in the full classical weak H1 form domain. Compactness
is the proved sphere Rellich theorem; the multiplier is actual V(x). -/

noncomputable section
open Bundle Manifold MeasureTheory Set Filter Metric
open scoped Manifold Topology ContDiff ENNReal BigOperators RealInnerProductSpace InnerProductSpace

namespace DFLSphere
open DifferentialGeometry
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DFLWeakH1Completion

section Multiplication
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Multiplication by the actual essentially bounded real function V. -/
def boundedPotentialMultiplication (V : X → ℝ) (hV : MemLp V ∞ μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 2 2 (hV.toLp V)

theorem boundedPotentialMultiplication_ae (V : X → ℝ) (hV : MemLp V ∞ μ)
    (f : Lp ℝ 2 μ) :
    boundedPotentialMultiplication V hV f =ᵐ[μ] fun x => V x*f x := by
  have hh := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (hV.toLp V) f
  filter_upwards [hh,hV.coeFn_toLp] with x hx hv
  change ((ContinuousLinearMap.mul ℝ ℝ).holder 2 (hV.toLp V) f : X → ℝ) x = _
  rw [hx,hv]
  rfl

theorem boundedPotentialMultiplication_inner (V : X → ℝ) (hV : MemLp V ∞ μ)
    (f h : Lp ℝ 2 μ) :
    ⟪boundedPotentialMultiplication V hV f,h⟫_ℝ = ∫ x, V x*f x*h x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedPotentialMultiplication_ae V hV f] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial]
  ring

theorem boundedPotentialMultiplication_symmetric (V : X → ℝ) (hV : MemLp V ∞ μ) :
    (boundedPotentialMultiplication V hV).IsSymmetric := by
  intro f h
  change ⟪boundedPotentialMultiplication V hV f,h⟫_ℝ = ⟪f,boundedPotentialMultiplication V hV h⟫_ℝ
  rw [boundedPotentialMultiplication_inner V hV f h]
  have hc : ⟪f,boundedPotentialMultiplication V hV h⟫_ℝ =
      ⟪boundedPotentialMultiplication V hV h,f⟫_ℝ := real_inner_comm _ _
  rw [hc, boundedPotentialMultiplication_inner V hV h f]
  apply integral_congr_ae
  filter_upwards [] with x
  ring
end Multiplication

private local instance (k : ℕ) : MeasurableSpace (RoundSphere k) := borel (RoundSphere k)
private local instance (k : ℕ) : BorelSpace (RoundSphere k) := ⟨rfl⟩

abbrev roundVolume (k : ℕ) :=
  riemannianVolumeMeasure (𝓡 (k+2)) (RoundSphere k) (roundSphereMetric k)

/-- The original gradient energy plus the pointwise potential energy. -/
def roundPotentialEnergy (k : ℕ) (V : RoundSphere k → ℝ)
    (U : H1Compl (roundSphereMetric k)) : ℝ :=
  ‖U‖^2-‖H1ComplToLp (roundSphereMetric k) U‖^2+
    ∫ x, V x*(H1ComplToLp (roundSphereMetric k) U x)^2 ∂roundVolume k

private local instance (k : ℕ) : IsFiniteMeasure (roundVolume k) :=
  riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (roundSphereMetric k)

private theorem round_continuous_memLp_top (k : ℕ) (V : RoundSphere k → ℝ)
    (hV : Continuous V) : MemLp V ∞ (roundVolume k) :=
  hV.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

set_option maxHeartbeats 800000 in
-- The actual metric and L² coercions in the full variational identity require additional elaboration steps.
/-- Actual lowest-value attainment, with no compactness, coercivity,
minimum, ground state, or eigenfunction premise. Continuity already suffices. -/
theorem round_potential_ground_exists (k : ℕ) (V : RoundSphere k → ℝ)
    (hV : Continuous V) :
    ∃ (lam : ℝ) (U : H1Compl (roundSphereMetric k)),
      ‖H1ComplToLp (roundSphereMetric k) U‖ = 1 ∧
      roundPotentialEnergy k V U = lam ∧
      (∀ W : H1Compl (roundSphereMetric k),
        lam*‖H1ComplToLp (roundSphereMetric k) W‖^2 ≤ roundPotentialEnergy k V W) ∧
      (∀ W : H1Compl (roundSphereMetric k),
        ⟪U,W⟫_ℝ - ⟪H1ComplToLp (roundSphereMetric k) U,H1ComplToLp (roundSphereMetric k) W⟫_ℝ + 
          (∫ x, V x*H1ComplToLp (roundSphereMetric k) U x*
            H1ComplToLp (roundSphereMetric k) W x ∂roundVolume k) =
        lam*⟪H1ComplToLp (roundSphereMetric k) U,H1ComplToLp (roundSphereMetric k) W⟫_ℝ) := by
  let J := H1ComplToLp (roundSphereMetric k)
  have hVtop := round_continuous_memLp_top k V hV
  let P := boundedPotentialMultiplication V hVtop
  have hJ0 : ∃ W : H1Compl (roundSphereMetric k), J W ≠ 0 := by
    refine ⟨smoothToH1Compl (roundSphereMetric k) (roundCoordinate k),?_⟩
    change H1ComplToLp (roundSphereMetric k) _ ≠ 0
    rw [H1ComplToLp_smoothToH1Compl]
    exact norm_pos_iff.mp (roundCoordinate_L2_norm_pos k)
  obtain ⟨lam,U,hUnorm,hweak,hmin⟩ := compact_potential_form_ground_exists J
    (H1ComplToLp_isCompactOperator (roundSphereMetric k)) hJ0 P
    (boundedPotentialMultiplication_symmetric V hVtop)
  have hform (W Z : H1Compl (roundSphereMetric k)) :
      potentialForm J P W Z = ⟪W,Z⟫_ℝ - ⟪J W,J Z⟫_ℝ + 
        ∫ x, V x*J W x*J Z x ∂roundVolume k := by
    unfold potentialForm
    change _ + ⟪boundedPotentialMultiplication V hVtop (J W),J Z⟫_ℝ = _
    rw [boundedPotentialMultiplication_inner V hVtop (J W) (J Z)]
  have hdiag (W : H1Compl (roundSphereMetric k)) :
      potentialForm J P W W = roundPotentialEnergy k V W := by
    rw [hform, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    unfold roundPotentialEnergy
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  refine ⟨lam,U,hUnorm,?_,?_,?_⟩
  · have hh := hweak U
    rw [hdiag, real_inner_self_eq_norm_sq, hUnorm] at hh
    simpa using hh
  · intro W
    rw [← hdiag]
    exact hmin W
  · intro W
    rw [← hform]
    exact hweak W

/-- The minimizer belongs to the actual distributional weak H1 space,
and its energy is the original gradient-plus-potential integral. The
comparison quantifier covers every classical weak H1 function. -/
theorem round_potential_weakH1_ground_exists (k : ℕ) (V : RoundSphere k → ℝ)
    (hV : Continuous V) :
    ∃ (lam : ℝ) (u : Lp ℝ 2 (roundVolume k))
      (G : ∀ x : RoundSphere k, TangentSpace (𝓡 (k+2)) x),
      ‖u‖ = 1 ∧ HasWeakRiemannianGradLp (roundSphereMetric k) (u : RoundSphere k → ℝ) G ∧
      MemLp (metricNorm (roundSphereMetric k) G) 2 (roundVolume k) ∧
      (∫ x, (roundSphereMetric k).inner x (G x) (G x) ∂roundVolume k)+
        (∫ x, V x*(u x)^2 ∂roundVolume k) = lam ∧
      ∀ (v : Lp ℝ 2 (roundVolume k))
        (F : ∀ x : RoundSphere k, TangentSpace (𝓡 (k+2)) x),
        HasWeakRiemannianGradLp (roundSphereMetric k) (v : RoundSphere k → ℝ) F →
        MemLp (metricNorm (roundSphereMetric k) F) 2 (roundVolume k) →
        lam*‖v‖^2 ≤ (∫ x, (roundSphereMetric k).inner x (F x) (F x) ∂roundVolume k)+
          (∫ x, V x*(v x)^2 ∂roundVolume k) := by
  obtain ⟨lam,U,hn,he,hmin,_⟩ := round_potential_ground_exists k V hV
  obtain ⟨G,hw,hGn,hE⟩ := H1ComplToLp_exists_weak_gradient_energy (roundSphereMetric k) U
  refine ⟨lam,H1ComplToLp (roundSphereMetric k) U,G,hn,hw,hGn,?_,?_⟩
  · unfold roundPotentialEnergy at he
    rw [hE] at he
    exact he
  · intro v F hv hFn
    obtain ⟨W,hW,hWE⟩ := weakH1_exists_completion_energy (roundSphereMetric k) v F hv hFn
    have hh := hmin W
    unfold roundPotentialEnergy at hh
    rw [hW,hWE] at hh
    exact hh

theorem round_completion_smooth_L2_pairing (k : ℕ)
    (U : H1Compl (roundSphereMetric k)) (φ : SmoothScalar (roundSphereMetric k)) :
    ⟪H1ComplToLp (roundSphereMetric k) U,smoothToLp (roundSphereMetric k) φ⟫_ℝ =
      ∫ x, H1ComplToLp (roundSphereMetric k) U x*φ.toFun x ∂roundVolume k := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [φ.memLp_two.coeFn_toLp] with x hx
  have hφ : (smoothToLp (roundSphereMetric k) φ : RoundSphere k → ℝ) x = φ.toFun x := hx
  simp only [hφ, RCLike.inner_apply, conj_trivial]
  ring


/-- The completion pairing is the actual distributional gradient pairing
against every smooth test function, using the proved weak gradient identity. -/
theorem round_completion_smooth_dirichlet (k : ℕ)
    (U : H1Compl (roundSphereMetric k))
    (G : ∀ x : RoundSphere k, TangentSpace (𝓡 (k+2)) x)
    (hG : HasWeakRiemannianGradLp (roundSphereMetric k)
      (H1ComplToLp (roundSphereMetric k) U : RoundSphere k → ℝ) G)
    (φ : SmoothScalar (roundSphereMetric k)) :
    ⟪U,smoothToH1Compl (roundSphereMetric k) φ⟫_ℝ -
      ⟪H1ComplToLp (roundSphereMetric k) U,smoothToLp (roundSphereMetric k) φ⟫_ℝ =
      ∫ x, (roundSphereMetric k).inner x (G x)
        (gradFun (roundSphereMetric k) φ.toFun x) ∂roundVolume k := by
  let g := roundSphereMetric k
  have hbridge := smoothToH1Compl_bilin_eq_lpFunctional φ U
  rw [H1ComplBilin_apply,lpFunctionalCLM_apply] at hbridge
  have hcomm : ⟪U,smoothToH1Compl g φ⟫_ℝ = ⟪smoothToH1Compl g φ,U⟫_ℝ := real_inner_comm _ _
  have hsub : smoothToLp g φ.oneSubLapClassical = smoothToLp g φ-smoothToLp g φ.laplacian := by
    have hm := (smoothToLp g).map_sub φ φ.oneSubLapClassical
    rw [φ.sub_oneSubLapClassical] at hm
    calc
      _ = smoothToLp g φ-(smoothToLp g φ-smoothToLp g φ.oneSubLapClassical) := by abel
      _ = _ := by rw [← hm]
  rw [hcomm,hbridge,hsub,inner_sub_right]
  have hp := hG.pairing_eq (gradG g φ.toContMDiffMap) (HasCompactSupport.of_compactSpace _)
  change (∫ x, g.inner x (G x) (gradFun g φ.toFun x) ∂roundVolume k) =
    -(∫ x, H1ComplToLp g U x * ΔG g φ.toContMDiffMap x ∂roundVolume k) at hp
  rw [round_completion_smooth_L2_pairing k U φ.laplacian]
  have hfun : φ.laplacian.toFun = ΔG g φ.toContMDiffMap := rfl
  rw [hfun, hp]
  ring

/-- The attained ground state satisfies the actual weak Schrödinger
operator equation on the true sphere, for every smooth test function. -/
theorem round_potential_weak_eigen_ground_exists (k : ℕ) (V : RoundSphere k → ℝ)
    (hV : Continuous V) :
    ∃ (lam : ℝ) (U : H1Compl (roundSphereMetric k))
      (G : ∀ x : RoundSphere k, TangentSpace (𝓡 (k+2)) x),
      ‖H1ComplToLp (roundSphereMetric k) U‖ = 1 ∧
      HasWeakRiemannianGradLp (roundSphereMetric k)
        (H1ComplToLp (roundSphereMetric k) U : RoundSphere k → ℝ) G ∧
      MemLp (metricNorm (roundSphereMetric k) G) 2 (roundVolume k) ∧
      roundPotentialEnergy k V U = lam ∧
      (∀ W : H1Compl (roundSphereMetric k),
        lam*‖H1ComplToLp (roundSphereMetric k) W‖^2 ≤ roundPotentialEnergy k V W) ∧
      ∀ φ : SmoothScalar (roundSphereMetric k),
        (∫ x, (roundSphereMetric k).inner x (G x)
          (gradFun (roundSphereMetric k) φ.toFun x) ∂roundVolume k)+
          (∫ x, V x*H1ComplToLp (roundSphereMetric k) U x*φ.toFun x ∂roundVolume k) =
          lam*(∫ x, H1ComplToLp (roundSphereMetric k) U x*φ.toFun x ∂roundVolume k) := by
  obtain ⟨lam,U,hn,he,hmin,hweak⟩ := round_potential_ground_exists k V hV
  obtain ⟨G,hw,hGn,_⟩ := H1ComplToLp_exists_weak_gradient_energy (roundSphereMetric k) U
  refine ⟨lam,U,G,hn,hw,hGn,he,hmin,?_⟩
  intro φ
  have hh := hweak (smoothToH1Compl (roundSphereMetric k) φ)
  rw [H1ComplToLp_smoothToH1Compl,round_completion_smooth_dirichlet k U G hw φ,
    round_completion_smooth_L2_pairing k U φ] at hh
  have hpot : (∫ x, V x*H1ComplToLp (roundSphereMetric k) U x*
      smoothToLp (roundSphereMetric k) φ x ∂roundVolume k) =
      ∫ x, V x*H1ComplToLp (roundSphereMetric k) U x*φ.toFun x ∂roundVolume k := by
    apply integral_congr_ae
    filter_upwards [φ.memLp_two.coeFn_toLp] with x hx
    have hφ : smoothToLp (roundSphereMetric k) φ x = φ.toFun x := hx
    rw [hφ]
  rw [hpot] at hh
  exact hh


/-- The manuscript's half-density tilt potential on the auxiliary sphere.
Its latitude is the actual ambient north-axis coordinate. -/
def roundTiltPotential (k : ℕ) (lam0 r a : ℝ) (x : RoundSphere k) : ℝ :=
  lam0+r^2/4*(1-((roundCoordinate k).toFun x)^2)-a*r*(roundCoordinate k).toFun x

theorem roundTiltPotential_continuous (k : ℕ) (lam0 r a : ℝ) :
    Continuous (roundTiltPotential k lam0 r a) := by
  have ht : Continuous (roundCoordinate k).toFun := (roundCoordinate k).smooth.continuous
  exact (continuous_const.add (continuous_const.mul (continuous_const.sub (ht.pow 2)))).sub
    (continuous_const.mul ht)

/-- The original fixed-domain tilted Rayleigh value is actually attained.
No ground profile, positive eigenfunction, or minimum is an input. -/
theorem round_tilt_minimum_attained (k : ℕ) (lam0 r a : ℝ) :
    ∃ (lam : ℝ) (U : H1Compl (roundSphereMetric k)),
      ‖H1ComplToLp (roundSphereMetric k) U‖ = 1 ∧
      roundPotentialEnergy k (roundTiltPotential k lam0 r a) U = lam ∧
      ∀ W : H1Compl (roundSphereMetric k),
        lam*‖H1ComplToLp (roundSphereMetric k) W‖^2 ≤
          roundPotentialEnergy k (roundTiltPotential k lam0 r a) W := by
  obtain ⟨lam,U,hn,he,hmin,_⟩ := round_potential_ground_exists k
    (roundTiltPotential k lam0 r a) (roundTiltPotential_continuous k lam0 r a)
  exact ⟨lam,U,hn,he,hmin⟩

end DFLSphere
