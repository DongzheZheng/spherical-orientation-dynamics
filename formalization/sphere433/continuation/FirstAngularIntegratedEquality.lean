import continuation.FullSphereFirstMeanZero

/-! Actual first minimizers saturate the original transverse norm and
angular/scalar energy bounds. These are the precise equality inputs for
the first eigenspace rigidity proof. -/
noncomputable section
set_option maxHeartbeats 1000000
open Bundle Manifold Set Filter Metric Module MeasureTheory
open scoped Manifold Topology ContDiff ENNReal RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DFLSphere DFLPhysicalGap DFLPhysicalLatitude DFLMeanSphere DFLCotSphere
open DFLTransverseSphere DFLFullSphereFirst DFLFullSphereMeanZero
namespace DFLFirstAngularEquality
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E=n+2)]
private local instance (p : sphere (0 : E) 1) : MeasurableSpace (PolarDir p) := borel (PolarDir p)
private local instance (p : sphere (0 : E) 1) : BorelSpace (PolarDir p) := ⟨rfl⟩
private local instance : MeasurableSpace (sphere (0 : E) 1) := borel (sphere (0 : E) 1)
private local instance : BorelSpace (sphere (0 : E) 1) := ⟨rfl⟩

/-- With vanishing true angular mean, the transverse norm is the whole
original weighted sphere norm. -/
theorem cotMean_zero_transverse_mass_eq (p : sphere (0 : E) 1)
    (f : C^∞⟮𝓡 (n+1),sphere (0 : E) 1;ℝ⟯) (r : ℝ) (hcot : ∀s,cotMean p f s=0) :
    (∫s : ℝ,cotTransverseMass p f r s)=weightedMass (n := n+1) (p : E) r f := by
  unfold weightedMass
  rw [cot_sphere_weighted_norm (n := n) p r f]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [cot_transverse_mass_eq,integral_const_mul]
  apply congrArg (fun z : ℝ => cotScalarDensity n r s*z)
  apply integral_congr_ae
  filter_upwards [] with y
  change (f (cotSpherePD (n := n) p (y,s))-cotMean p f s)^2=(f (cotSpherePD (n := n) p (y,s)))^2
  rw [hcot,sub_zero]

/-- With vanishing true angular mean, the deviation energy is exactly the
original whole-sphere weighted Dirichlet energy. -/
theorem cotMean_zero_deviation_energy_eq (p : sphere (0 : E) 1)
    (f : C^∞⟮𝓡 (n+1),sphere (0 : E) 1;ℝ⟯) (r : ℝ) (hcot : ∀s,cotMean p f s=0) :
    weightedEnergy (n := n+1) (p : E) r f=(∫s : ℝ,cotDeviationEnergy p f r s) := by
  have hF : (cotDeviation p f : PolarDir p × ℝ → ℝ)=cotSpherePullback p f := by
    funext q
    change f (cotSpherePD (n := n) p q)-cotMean p f q.2=f (cotSpherePD (n := n) p q)
    rw [hcot,sub_zero]
  unfold weightedEnergy
  rw [cot_weighted_energy_product p r f]
  apply integral_congr_ae
  filter_upwards [] with s
  unfold cotDeviationEnergy
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  exact congrArg (fun h : PolarDir p × ℝ → ℝ => normGradSqFun (cotProductMetric (n := n) p) h (y,s)) hF.symm

/-- Every actual normalized smooth first minimum saturates the true
angular Poincaré reduction after the genuine mean is eliminated. -/
theorem actual_gap_minimizer_angular_energy_equality (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r)
    (f : C^∞⟮𝓡 (k+1),PhysicalSphere k;ℝ⟯)
    (hM : weightedMass (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=1)
    (hm : weightedMean (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=0)
    (hE : weightedEnergy (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=
      weightedGap (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r) :
    (∫s : ℝ,cotDeviationEnergy (canonicalAxisSphere k) f r s)=
      ∫s : ℝ,cotDeviationReducedEnergy (canonicalAxisSphere k) f r s := by
  let p := canonicalAxisSphere k
  let lam := weightedGap (n := k+1) (p : PhysicalAmbient k) r
  have hcot := actual_gap_minimizer_angular_mean_zero k hk r hr f hM hm hE
  have hMass : (∫s : ℝ,cotTransverseMass p f r s)=1 :=
    (cotMean_zero_transverse_mass_eq p f r hcot).trans hM
  have hEnergy : (∫s : ℝ,cotDeviationEnergy p f r s)=lam :=
    (cotMean_zero_deviation_energy_eq p f r hcot).symm.trans hE
  have hGap : lam=roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2) := by
    apply le_antisymm
    · simpa only [Nat.cast_add,Nat.cast_one] using
        actual_weighted_gap_le_transverse_of_unit_axis (n := k+1) (p : PhysicalAmbient k)
          (by simp [p,canonicalAxisSphere]) r
    · exact actual_weighted_gap_ge_transverse k hk r hr
  have hLower := cot_transverse_first_minimum_lower hk p f r
  simp_rw [cot_transverse_reduced_eq] at hLower
  rw [hMass,mul_one] at hLower
  have hUpper := integral_mono (cot_deviation_reduced_energy_integrable hk p f r)
    (cot_deviation_energy_integrable p f r) (cot_deviation_reduced_slice_lower hk p f r)
  apply le_antisymm
  · rw [hEnergy,hGap]
    simpa only [Nat.cast_add,Nat.cast_one] using hLower
  · exact hUpper

/-- The same actual first minimum also saturates the original integrated
one-dimensional ground-state inequality on the angular fibers. -/
theorem actual_gap_minimizer_scalar_energy_equality (k : ℕ) (hk : 1≤k) (r : ℝ) (hr : 0<r)
    (f : C^∞⟮𝓡 (k+1),PhysicalSphere k;ℝ⟯)
    (hM : weightedMass (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=1)
    (hm : weightedMean (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=0)
    (hE : weightedEnergy (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r f=
      weightedGap (n := k+1) (EuclideanSpace.single 0 1 : PhysicalAmbient k) r) :
    (∫s : ℝ,cotTransverseReduced (canonicalAxisSphere k) f r s)=
      roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2)*
        ∫s : ℝ,cotTransverseMass (canonicalAxisSphere k) f r s := by
  let p := canonicalAxisSphere k
  have hcot := actual_gap_minimizer_angular_mean_zero k hk r hr f hM hm hE
  have hMass : (∫s : ℝ,cotTransverseMass p f r s)=1 :=
    (cotMean_zero_transverse_mass_eq p f r hcot).trans hM
  have hEnergy : (∫s : ℝ,cotDeviationEnergy p f r s)=
      weightedGap (n := k+1) (p : PhysicalAmbient k) r :=
    (cotMean_zero_deviation_energy_eq p f r hcot).symm.trans hE
  have hEq := actual_gap_minimizer_angular_energy_equality k hk r hr f hM hm hE
  have hGap : weightedGap (n := k+1) (p : PhysicalAmbient k) r=
      roundTiltMinimum (k+1) (k+1 : ℝ) r ((k+1 : ℝ)/2) := by
    apply le_antisymm
    · simpa only [Nat.cast_add,Nat.cast_one] using
        actual_weighted_gap_le_transverse_of_unit_axis (n := k+1) (p : PhysicalAmbient k)
          (by simp [p,canonicalAxisSphere]) r
    · exact actual_weighted_gap_ge_transverse k hk r hr
  simp_rw [cot_transverse_reduced_eq]
  rw [hMass,mul_one,← hEq,hEnergy,hGap]

end DFLFirstAngularEquality
