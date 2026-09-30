import DFL.Spectral.WholeSphereCore
import DFL.Spectral.CoordinateTrial

/-!
# Coordinate functions in the original whole-sphere form core
-/

namespace DFL.Spectral

open MeasureTheory InnerProductSpace

noncomputable section

def coordinateCore (d : ℕ) (i : Fin (d + 1)) : SphereC1Core d where
  toFun := fun x => x i
  smooth := by
    exact contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (i := i) (n := 1)

theorem coordinateCore_value (d : ℕ) (i : Fin (d + 1))
    (x : SpherePoint d) :
    coreValue d (coordinateCore d i) x = sphereCoordinate d i x := rfl

private theorem ambient_coordinate_gradient (d : ℕ)
    (i : Fin (d + 1)) (x : Ambient d) :
    gradient (fun y : Ambient d => y i) x =
      EuclideanSpace.single i (1 : ℝ) := by
  have hdual : toDual ℝ (Ambient d) (EuclideanSpace.single i (1 : ℝ)) =
      EuclideanSpace.proj (𝕜 := ℝ) i := by
    ext v
    simpa using EuclideanSpace.inner_single_left i (1 : ℝ) v
  have hder : HasFDerivAt (fun y : Ambient d => y i)
      (EuclideanSpace.proj (𝕜 := ℝ) i) x := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := x)
  exact (hasGradientAt_iff_hasFDerivAt.mpr (hdual ▸ hder)).gradient

theorem coordinateCore_tangentGradient (d : ℕ)
    (i : Fin (d + 1)) (x : SpherePoint d) :
    coreTangentGradient d (coordinateCore d i) x =
      coordinateTangentGradient d i x := by
  simp only [coreTangentGradient, coordinateCore, coordinateTangentGradient,
    ambient_coordinate_gradient, sphereCoordinate]
  have hsingle : inner ℝ (EuclideanSpace.single i (1 : ℝ)) x.1 = x.1 i := by
    simpa using EuclideanSpace.inner_single_left i (1 : ℝ) x.1
  rw [hsingle]

/-- The global form energy of a physical coordinate on the zero-field
sphere equals the earlier pointwise-projected trial energy. -/
theorem coordinateCore_energy_zero (d : ℕ) (i : Fin (d + 1)) :
    coreEnergy d 0 (coordinateCore d i) =
      (d : ℝ) / (d + 1 : ℝ) := by
  unfold coreEnergy
  simp_rw [coordinateCore_tangentGradient]
  exact sphereCoordinate_tangent_energy_zero d i

end

end DFL.Spectral
