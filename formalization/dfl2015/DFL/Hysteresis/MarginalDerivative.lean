import DFL.Hysteresis.MomentDerivative

/-!
# Differentiating the original spherical moments

The proofs differentiate the one-dimensional marginal from `DFL.Targets`
under its defining integral, including the integrable circle endpoint
singularity.  They establish regularity of the actual feedback curve on the
positive field axis, without assuming any monotonicity or single-valley claim.
-/

namespace DFL

open MeasureTheory Filter
open scoped Interval Topology

noncomputable section

/-- The first field derivative of the original first moment is the second
moment, in every sphere dimension `n ≥ 2`. -/
theorem firstMoment_hasDerivAt_secondMoment (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    HasDerivAt (firstMoment n) (secondMoment n r) r := by
  let s : Set ℝ := Set.Ioo (r - 1) (r + 1)
  let F : ℝ → ℝ → ℝ := fun x t => t * marginalWeight n x t
  let F' : ℝ → ℝ → ℝ := fun x t => t ^ 2 * marginalWeight n x t
  let bound : ℝ → ℝ := fun t => Real.exp (|r| + 1) * marginalWeight n 0 t
  have hs : s ∈ 𝓝 r := by
    apply IsOpen.mem_nhds isOpen_Ioo
    dsimp [s]
    constructor <;> dsimp <;> linarith
  have hF_meas : ∀ᶠ x in 𝓝 r,
      AEStronglyMeasurable (F x) (volume.restrict (Ι (-1 : ℝ) 1)) := by
    filter_upwards [] with x
    exact (firstMoment_intervalIntegrable n hn x).def'.aestronglyMeasurable
  have hF_int : IntervalIntegrable (F r) volume (-1 : ℝ) 1 :=
    firstMoment_intervalIntegrable n hn r
  have hF'_meas : AEStronglyMeasurable (F' r)
      (volume.restrict (Ι (-1 : ℝ) 1)) :=
    (secondMoment_intervalIntegrable n hn r).def'.aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι (-1 : ℝ) 1 →
      ∀ x ∈ s, ‖F' x t‖ ≤ bound t := by
    filter_upwards [] with t ht x hx
    have ht' : t ∈ Set.Ioc (-1 : ℝ) 1 := by
      simpa only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    have ht_abs : |t| ≤ 1 := abs_le.mpr ⟨ht'.1.le, ht'.2⟩
    calc
      ‖F' x t‖ = |t| * ‖t * marginalWeight n x t‖ := by
        simp [F', pow_two, norm_mul, Real.norm_eq_abs, mul_assoc]
      _ ≤ 1 * ‖t * marginalWeight n x t‖ :=
        mul_le_mul_of_nonneg_right ht_abs (norm_nonneg _)
      _ = ‖t * marginalWeight n x t‖ := one_mul _
      _ ≤ bound t := marginalWeight_deriv_bound n r x t hx ht'
  have bound_integrable : IntervalIntegrable bound volume (-1 : ℝ) 1 :=
    (marginalWeight_intervalIntegrable n hn 0).const_mul _
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι (-1 : ℝ) 1 →
      ∀ x ∈ s, HasDerivAt (fun x => F x t) (F' x t) x := by
    filter_upwards [] with t ht x hx
    convert (marginalWeight_hasDerivAt n x t).const_mul t using 1; ring
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hF_meas hF_int hF'_meas h_bound bound_integrable h_diff
  exact h.2

/-- The original spherical orientation mean is differentiable at all fields. -/
theorem orientationMean_differentiableAt (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    DifferentiableAt ℝ (orientationMean n) r := by
  exact (firstMoment_hasDerivAt_secondMoment n hn r).differentiableAt.div
    (partition_hasDerivAt_firstMoment n hn r).differentiableAt
    (ne_of_gt (partition_pos n hn r))

/-- The orientation response is the variance of the first-coordinate law,
expressed directly through its two unnormalized moments. -/
theorem orientationMean_deriv (n : ℕ) (hn : 2 ≤ n) (r : ℝ) :
    deriv (orientationMean n) r =
      secondMoment n r / partition n r - (orientationMean n r) ^ 2 :=
  orientationMean_deriv_of_moment_derivs n r
    (partition_hasDerivAt_firstMoment n hn r)
    (firstMoment_hasDerivAt_secondMoment n hn r)
    (ne_of_gt (partition_pos n hn r))

/-- The original equilibrium density curve is differentiable on its positive
physical field domain. -/
theorem equilibriumDensity_differentiableAt (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ (equilibriumDensity n) r := by
  have harg : 1 + 4 * r ≠ 0 := by linarith
  have hroot : DifferentiableAt ℝ (fun x : ℝ => Real.sqrt (1 + 4 * x)) r :=
    ((show DifferentiableAt ℝ (fun x : ℝ => 1 + 4 * x) r by fun_prop).hasDerivAt.sqrt
      harg).differentiableAt
  have hj : DifferentiableAt ℝ inverseAlignment r := by
    unfold inverseAlignment
    exact (hroot.sub_const 1).div_const 2
  exact hj.div (orientationMean_differentiableAt n hn r)
    (ne_of_gt (orientationMean_pos n hn hr))

/-- Every analytic clause of `MarginalWellDefined` now follows from the
original marginal, rather than being postulated. -/
theorem marginalWellDefined (n : ℕ) (hn : 2 ≤ n) :
    MarginalWellDefined n := by
  intro r hr
  exact ⟨marginalWeight_intervalIntegrable n hn r,
    firstMoment_intervalIntegrable n hn r,
    partition_pos n hn r,
    orientationMean_pos n hn hr,
    equilibriumDensity_differentiableAt n hn hr⟩

end

end DFL
