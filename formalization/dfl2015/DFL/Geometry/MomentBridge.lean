import DFL.Geometry.SphereMeasure
import DFL.Hysteresis.Conjecture

/-!
# Exact interface between the original sphere and the marginal formula

The interface lemmas below are conditional on two genuine geometric moment
identities. Those premises are discharged in `PhysicalSphereAll.lean` from
the proved first-coordinate pushforward of `volume.toSphere` for every
ambient dimension `n ≥ 2`. This file isolates the analytic transfer to
the mean and equilibrium density.
-/

namespace DFL.Geometry

noncomputable section

/-- The original physical-sphere orientation mean, directly from its area
measure and external-field partition function. -/
def sphereOrientationMean (n : ℕ) (hn : 0 < n) (r : ℝ) : ℝ :=
  sphereFirstMoment n hn r / spherePartition n hn r

/-- The original physical-sphere equilibrium density curve. -/
def sphereEquilibriumDensity (n : ℕ) (hn : 0 < n) (r : ℝ) : ℝ :=
  DFL.inverseAlignment r / sphereOrientationMean n hn r

/-- Precisely the common-constant moment relation supplied by a
first-coordinate beta pushforward. The constant must be independent of
the field. It is proved for all `n≥2` in `PhysicalSphereAll.lean`. -/
def SphereMomentBridge (n : ℕ) (hn : 0 < n) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ,
    spherePartition n hn r = C * DFL.partition n r ∧
    sphereFirstMoment n hn r = C * DFL.firstMoment n r

/-- If the actual sphere moments are those of the paper's marginal, the
physical and formula-level orientation means agree at every field. -/
theorem sphereOrientationMean_eq_of_moment_bridge
    (n : ℕ) (hn : 2 ≤ n) (hbridge : SphereMomentBridge n (by omega))
    (r : ℝ) :
    sphereOrientationMean n (by omega) r = DFL.orientationMean n r := by
  obtain ⟨C, hC, hmoment⟩ := hbridge
  obtain ⟨hZ, hM⟩ := hmoment r
  unfold sphereOrientationMean DFL.orientationMean
  rw [hZ, hM]
  have hCne : C ≠ 0 := ne_of_gt hC
  have hZne : DFL.partition n r ≠ 0 := ne_of_gt (DFL.partition_pos n hn r)
  field_simp

/-- The same geometric bridge identifies the *entire* physical equilibrium
density curve, including its derivatives at positive fields. -/
theorem sphereEquilibriumDensity_eq_of_moment_bridge
    (n : ℕ) (hn : 2 ≤ n) (hbridge : SphereMomentBridge n (by omega)) :
    sphereEquilibriumDensity n (by omega) = DFL.equilibriumDensity n := by
  funext r
  unfold sphereEquilibriumDensity DFL.equilibriumDensity
  rw [sphereOrientationMean_eq_of_moment_bridge n hn hbridge r]

/-- Historical single-valley statement phrased on the actual physical
sphere.  Its formula-level counterpart was proved in `Conjecture.lean`. -/
def SphereIsUnimodal (n : ℕ) (hn : 0 < n) : Prop :=
  ∃ rStar : ℝ,
    0 < rStar ∧
    StrictAntiOn (sphereEquilibriumDensity n hn) (Set.Ioc 0 rStar) ∧
    StrictMonoOn (sphereEquilibriumDensity n hn) (Set.Ici rStar) ∧
    deriv (sphereEquilibriumDensity n hn) rStar = 0 ∧
    (∀ r : ℝ, 0 < r →
      deriv (sphereEquilibriumDensity n hn) r = 0 → r = rStar)

/-- The exact original-sphere single-valley theorem follows once the
geometric moment bridge is supplied. `PhysicalSphereAll.lean` provides that
bridge unconditionally for every `n≥2`. -/
theorem sphere_isUnimodal_of_moment_bridge
    (n : ℕ) (hn : 2 ≤ n) (hbridge : SphereMomentBridge n (by omega)) :
    SphereIsUnimodal n (by omega) := by
  have heq := sphereEquilibriumDensity_eq_of_moment_bridge n hn hbridge
  simpa only [SphereIsUnimodal, heq, DFL.IsUnimodal] using
    (DFL.dfl2015_unimodality_formula n hn)

end

end DFL.Geometry
