import continuation.RoundSphereActualTiltProfile
import DFLSphere433.LatitudePiconeGround

/-! Actual full-sphere positive grounds produce the manuscript's original
normalized latitude ground structure, for every M ≥ 2 and all real
parameters. Picone supplies the one-dimensional Rayleigh minimum. -/
noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped Interval
namespace DFL.Spectral
open DFLSphere

/-- The manuscript's normalized C² latitude core Rayleigh values, with
its original fixed weight and exact half-density operator. -/
def originalTiltSmoothRayleighValues (M : ℕ) (lam0 r a : ℝ) : Set ℝ :=
  {q | ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧ latitudeNorm M 0 v = 1 ∧
    q = tiltPair M lam0 r a v v}

def originalTiltSmoothMinimum (M : ℕ) (lam0 r a : ℝ) : ℝ :=
  sInf (originalTiltSmoothRayleighValues M lam0 r a)

/-- The original positive normalized ground exists at the actual full H¹
sphere minimum. No ground existence, Rayleigh principle, zonality, pole
regularity, or spectral ordering is an input. -/
theorem original_tilt_ground_exists_ge_two (M : ℕ) (hM : 2 ≤ M)
    (lam0 r a : ℝ) :
    ∃ u : ℝ → ℝ,
      IsTiltGroundProfile M lam0 r a (roundTiltMinimum (M-2) lam0 r a) u ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, 0 < u t := by
  obtain ⟨v,hv,hpos,heig⟩ := round_tilt_positive_C2_eigenprofile_exists (M-2) lam0 r a
  have hdim : M-2+2 = M := by omega
  rw [hdim] at heig
  obtain ⟨u,hu,hup,_⟩ := positive_tilt_eigenprofile_normalized_ground M hM lam0 r a
    (roundTiltMinimum (M-2) lam0 r a) v hv hpos heig
  exact ⟨u,hu,hup⟩

/-- An original normalized eigenprofile has its actual Rayleigh energy. -/
theorem original_tilt_ground_energy (M : ℕ) (lam0 r a lam : ℝ) (u : ℝ → ℝ)
    (hu : IsTiltGroundProfile M lam0 r a lam u) :
    tiltPair M lam0 r a u u = lam := by
  unfold tiltPair
  calc
    _ = ∫ t in (-1 : ℝ)..1, lam*(radialWeight M 0 t*(u t)^2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htcc : t ∈ Icc (-1 : ℝ) 1 := by simpa using ht
      dsimp only
      rw [hu.eigen t htcc]
      ring
    _ = lam*latitudeNorm M 0 u := by rw [intervalIntegral.integral_const_mul]; rfl
    _ = lam := by rw [hu.normalized,mul_one]

/-- Picone and the actual positive ground identify the original latitude
core minimum with the true full-domain sphere minimum, without requiring
a separate measure-disintegration premise. -/
theorem originalTiltSmoothMinimum_eq_round (M : ℕ) (hM : 2 ≤ M)
    (lam0 r a : ℝ) :
    originalTiltSmoothMinimum M lam0 r a = roundTiltMinimum (M-2) lam0 r a := by
  obtain ⟨u,hu,_⟩ := original_tilt_ground_exists_ge_two M hM lam0 r a
  have hleast : roundTiltMinimum (M-2) lam0 r a ∈
      lowerBounds (originalTiltSmoothRayleighValues M lam0 r a) := by
    rintro q ⟨v,hv,hn,rfl⟩
    simpa only [hn,mul_one] using hu.rayleigh v hv
  have hmem : roundTiltMinimum (M-2) lam0 r a ∈
      originalTiltSmoothRayleighValues M lam0 r a :=
    ⟨u,hu.smooth,hu.normalized,(original_tilt_ground_energy M lam0 r a _ u hu).symm⟩
  exact le_antisymm (csInf_le ⟨_,hleast⟩ hmem) (le_csInf ⟨_,hmem⟩ hleast)

/-- Actual attainment in the exact original one-dimensional core. -/
theorem originalTiltSmoothMinimum_attained (M : ℕ) (hM : 2 ≤ M)
    (lam0 r a : ℝ) :
    ∃ u : ℝ → ℝ, IsTiltGroundProfile M lam0 r a (originalTiltSmoothMinimum M lam0 r a) u ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, 0 < u t := by
  rw [originalTiltSmoothMinimum_eq_round M hM lam0 r a]
  exact original_tilt_ground_exists_ge_two M hM lam0 r a

private theorem actual_ground_family (M : ℕ) (hM : 2 ≤ M) (lam0 r : ℝ) :
    ∀ a : ℝ, ∃ u : ℝ → ℝ,
      IsTiltGroundProfile M lam0 r a (originalTiltSmoothMinimum M lam0 r a) u := by
  intro a
  obtain ⟨u,hu,_⟩ := originalTiltSmoothMinimum_attained M hM lam0 r a
  exact ⟨u,hu⟩

/-- Original two-endpoint eigen-equation proof of strict tilt concavity,
now with actual existence and minimum hypotheses discharged. -/
theorem original_tilt_minimum_strict_concave (M : ℕ) (hM : 2 ≤ M)
    (lam0 r : ℝ) (hr : 0 < r) (a b s : ℝ) (hab : a ≠ b) (hs : 0 < s) (hs1 : s < 1) :
    s*originalTiltSmoothMinimum M lam0 r a+(1-s)*originalTiltSmoothMinimum M lam0 r b <
      originalTiltSmoothMinimum M lam0 r (s*a+(1-s)*b) :=
  tilt_ground_energy_strict_concave M hM lam0 r hr
    (originalTiltSmoothMinimum M lam0 r) (actual_ground_family M hM lam0 r) a b s hab hs hs1

theorem original_tilt_minimum_even (M : ℕ) (hM : 2 ≤ M) (lam0 r a : ℝ) :
    originalTiltSmoothMinimum M lam0 r (-a) = originalTiltSmoothMinimum M lam0 r a :=
  tilt_ground_energy_even M lam0 r (originalTiltSmoothMinimum M lam0 r)
    (actual_ground_family M hM lam0 r) a

/-- Reflection and original strict concavity prove the whole nonnegative
axis tilt ordering, including its zero endpoint. -/
theorem original_tilt_minimum_strict_decreasing_nonnegative (M : ℕ) (hM : 2 ≤ M)
    (lam0 r : ℝ) (hr : 0 < r) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    originalTiltSmoothMinimum M lam0 r b < originalTiltSmoothMinimum M lam0 r a :=
  tilt_ground_energy_strict_decreasing_nonnegative M hM lam0 r hr
    (originalTiltSmoothMinimum M lam0 r) (actual_ground_family M hM lam0 r) a b ha hab

/-- The manuscript's strict auxiliary radial/transverse ground ordering,
now for actual minima, without an input ground-family hypothesis. -/
theorem original_radial_transverse_actual_ground_ordering (d : ℕ) (hd : 2 ≤ d)
    (r : ℝ) (hr : 0 < r) :
    roundTiltMinimum d (d : ℝ) r ((d : ℝ)/2) <
      roundTiltMinimum d (d : ℝ) r (((d : ℝ)-2)/2) := by
  have hg := original_radial_transverse_ground_ordering d hd r hr
    (originalTiltSmoothMinimum (d+2) (d : ℝ) r)
    (actual_ground_family (d+2) (by omega) (d : ℝ) r)
  simpa only [originalTiltSmoothMinimum_eq_round (d+2) (by omega),Nat.add_sub_cancel] using hg

end DFL.Spectral
