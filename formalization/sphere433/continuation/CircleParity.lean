import continuation.CircleOddEigenvalue
import continuation.ActualRadialCandidate
import continuation.SphereWeightedSymmetry

/-! The original circle even/odd reflection split is an actual smooth
weighted eigenfunction split. It proves the lower bound for every genuine
nonzero positive-eigenvalue smooth circle state, including the angular
zero-dimensional endpoint omitted by higher-dimensional coercivity. -/
noncomputable section
set_option maxHeartbeats 1000000
open Set Filter Function Metric Manifold Bundle Module
open scoped Topology ContDiff Manifold RealInnerProductSpace InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open DFLPhysicalLatitude DFLSphere DFLTransverseSphere DFLGroundSymmetry
open DFLWeightedSymmetry DFLActualRadial DFL.Spectral
namespace DFLCircleOdd

/-- Actual axis reflection is involutive on the true circle. -/
theorem circleReflection_involutive : Function.Involutive circleReflection := by
  intro x
  apply circle_ext
  · rw [circleReflection_coord0,circleReflection_coord0]
  · rw [circleReflection_coord1,circleReflection_coord1,neg_neg]

def CircleEven (u : Circle → ℝ) : Prop := ∀ x, u (circleReflection x) = u x

/-- On the actual circle, even reflection states are exactly zonal
states, by the proven two-point latitude fibre geometry. -/
theorem circle_even_constant_on_latitudes (u : Circle → ℝ) (hu : CircleEven u) :
    PhysicalConstantOnLatitudes 0 u := by
  intro x y hxy
  have hc : ∀ z : Circle, (physicalCoordinate 0).toFun z = (z : CircleAmbient) 0 := by
    intro z
    simp [physicalCoordinate,innerCoordFun,EuclideanSpace.inner_single_left]
  rw [hc x,hc y] at hxy
  rcases circle_same_latitude x y hxy with rfl | rfl
  · rfl
  · exact hu y

private theorem circleReflection_axis : circleReflectionEquiv circleAxis = circleAxis :=
  (ℝ ∙ circleAxis).reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self _)

def circleReflected (u : C^∞⟮𝓡 1, Circle; ℝ⟯) : C^∞⟮𝓡 1, Circle; ℝ⟯ :=
  orthogonalPullback circleReflectionEquiv u

def circleEvenPart (u : C^∞⟮𝓡 1, Circle; ℝ⟯) : C^∞⟮𝓡 1, Circle; ℝ⟯ :=
  ⟨fun x => (1/2)*u x+(1/2)*circleReflected u x,
    (contMDiff_const.mul u.contMDiff).add (contMDiff_const.mul (circleReflected u).contMDiff)⟩

def circleOddPart (u : C^∞⟮𝓡 1, Circle; ℝ⟯) : C^∞⟮𝓡 1, Circle; ℝ⟯ :=
  ⟨fun x => (1/2)*u x+(-1/2)*circleReflected u x,
    (contMDiff_const.mul u.contMDiff).add (contMDiff_const.mul (circleReflected u).contMDiff)⟩

/-- The actual smooth parity components sum to the original state. -/
theorem circle_even_odd_sum (u : C^∞⟮𝓡 1, Circle; ℝ⟯) (x : Circle) :
    circleEvenPart u x+circleOddPart u x = u x := by
  change ((1/2)*u x+(1/2)*u (circleReflection x))+
    ((1/2)*u x+(-1/2)*u (circleReflection x)) = _
  ring

theorem circle_evenPart_even (u : C^∞⟮𝓡 1, Circle; ℝ⟯) : CircleEven (circleEvenPart u) := by
  intro x
  change (1/2)*u (circleReflection x)+(1/2)*u (circleReflection (circleReflection x)) =
    (1/2)*u x+(1/2)*u (circleReflection x)
  rw [circleReflection_involutive x]
  ring

theorem circle_oddPart_odd (u : C^∞⟮𝓡 1, Circle; ℝ⟯) : CircleOdd (circleOddPart u) := by
  intro x
  change (1/2)*u (circleReflection x)+(-1/2)*u (circleReflection (circleReflection x)) =
    -((1/2)*u x+(-1/2)*u (circleReflection x))
  rw [circleReflection_involutive x]
  ring

/-- Every nonzero actual state has a nonzero actual parity component. -/
theorem circle_nonzero_even_or_odd (u : C^∞⟮𝓡 1, Circle; ℝ⟯)
    (hne : ∃ x, u x ≠ 0) :
    (∃ x, circleEvenPart u x ≠ 0) ∨ ∃ x, circleOddPart u x ≠ 0 := by
  by_cases he : ∃ x, circleEvenPart u x ≠ 0
  · exact Or.inl he
  · obtain ⟨x,hx⟩ := hne
    have hex : circleEvenPart u x = 0 := by by_contra hz; exact he ⟨x,hz⟩
    refine Or.inr ⟨x,?_⟩
    intro hox
    have hh := circle_even_odd_sum u x
    rw [hex,hox] at hh
    exact hx (by simpa only [zero_add] using hh.symm)

/-- The true weighted circle operator commutes with its actual reflection. -/
theorem circle_reflection_weightedRoundApply (r : ℝ)
    (u : C^∞⟮𝓡 1, Circle; ℝ⟯) (x : Circle) :
    weightedRoundApply (n := 1) circleAxis r (circleReflected u) x =
      weightedRoundApply (n := 1) circleAxis r u (circleReflection x) :=
  orthogonalPullback_weightedRoundApply circleAxis r circleReflectionEquiv circleReflection_axis u x

/-- The reflected smooth state obeys the actual same weighted eigen-PDE. -/
theorem circle_reflected_eigen (r lam : ℝ) (u : C^∞⟮𝓡 1, Circle; ℝ⟯)
    (heig : ∀ x, weightedRoundApply (n := 1) circleAxis r u x = lam*u x) :
    ∀ x, weightedRoundApply (n := 1) circleAxis r (circleReflected u) x = lam*circleReflected u x := by
  intro x
  rw [circle_reflection_weightedRoundApply r u x,heig]
  rfl

/-- Both actual smooth parity projections remain genuine eigenstates;
no commutation or operator linearity is supplied as an input. -/
theorem circle_parity_eigen (r lam : ℝ) (u : C^∞⟮𝓡 1, Circle; ℝ⟯)
    (heig : ∀ x, weightedRoundApply (n := 1) circleAxis r u x = lam*u x) :
    (∀ x, weightedRoundApply (n := 1) circleAxis r (circleEvenPart u) x = lam*circleEvenPart u x) ∧
    (∀ x, weightedRoundApply (n := 1) circleAxis r (circleOddPart u) x = lam*circleOddPart u x) := by
  have hRe := circle_reflected_eigen r lam u heig
  constructor <;> intro x
  · change weightedRoundApply (n := 1) circleAxis r
      (fun y => (1/2)*u y+(1/2)*circleReflected u y) x = _
    rw [weightedRoundApply_linear circleAxis r (1/2) (1/2) u (circleReflected u) x,heig,hRe]
    change (1/2)*(lam*u x)+(1/2)*(lam*circleReflected u x) =
      lam*((1/2)*u x+(1/2)*circleReflected u x)
    ring
  · change weightedRoundApply (n := 1) circleAxis r
      (fun y => (1/2)*u y+(-1/2)*circleReflected u y) x = _
    rw [weightedRoundApply_linear circleAxis r (1/2) (-1/2) u (circleReflected u) x,heig,hRe]
    change (1/2)*(lam*u x)+(-1/2)*(lam*circleReflected u x) =
      lam*((1/2)*u x+(-1/2)*circleReflected u x)
    ring

/-- Every actual nonzero smooth positive-eigenvalue circle state obeys
the actual first-transverse minimum lower bound. Even and odd projection,
both-pole profiles, actual commutation, and all minimum inputs are proved. -/
theorem actual_circle_positive_eigenvalue_ge_transverse_ground (r lam : ℝ)
    (hlam : 0 < lam) (u : C^∞⟮𝓡 1, Circle; ℝ⟯)
    (heig : ∀ x, weightedRoundApply (n := 1) circleAxis r u x = lam*u x)
    (hne : ∃ x, u x ≠ 0) :
    roundTiltMinimum 1 1 r (1/2) ≤ lam := by
  have he := circle_parity_eigen r lam u heig
  rcases circle_nonzero_even_or_odd u hne with hE | hO
  · have hlat := circle_even_constant_on_latitudes _ (circle_evenPart_even u)
    have hlow := actual_radial_eigenvalue_ge_actual_ground 0 r lam (ne_of_gt hlam)
      (circleEvenPart u) hlat he.1 hE
    have hlow' : roundTiltMinimum 1 1 r (1/2-1) ≤ lam := by
      simpa only [Nat.zero_add,Nat.cast_zero,zero_add] using hlow
    rw [circle_radial_transverse_actual_ground_eq r] at hlow'
    exact hlow' 
  · exact actual_circle_odd_eigenvalue_ge_transverse_ground r lam (circleOddPart u)
      (circle_oddPart_odd u) he.2 hO

end DFLCircleOdd
