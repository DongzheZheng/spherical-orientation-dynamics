import DFL.Targets

/-!
# The original angular GCI target of DFL 2015, Conjecture 5.1

Here `n` is the ambient Euclidean dimension of the 2015 article (`n ≥ 2`),
not the sphere dimension `d = n - 1` in the Chinese JPhysA manuscript.
The original coefficient is defined directly by angular integrals of the
original weak solution `g`; no unconstrained auxiliary amplitude is used.

`AngularEnergyDomain` uses the one-dimensional absolutely continuous
representative characterization of the source's weighted `H¹₀` condition.
`ClassicalEnergyDomainBridge.lean` proves its equivalence with the
conventional smooth function/derivative L² graph completion of H¹₀,
including genuine C_c∞ density and the original singular L² condition.
The proposition at the end of this file declares the target;
`ComparisonAll.lean` proves it.
-/

namespace DFL.GCI

open MeasureTheory
open scoped Interval

noncomputable section

/-- A representative of an angular function and the derivative of its
weighted `H¹₀` representative.  The latter is not a free unrelated field:
`AngularEnergyDomain` requires the exact integral reconstruction. -/
structure AngularState where
  g : ℝ → ℝ
  scaledDerivative : ℝ → ℝ

/-- The power `(n - 2)/2` in the original `H¹₀` condition. -/
def halfPower (n : ℕ) : ℝ := ((n : ℝ) - 2) / 2

/-- The original weighted `H¹₀` representative. -/
def scaledFunction (n : ℕ) (s : AngularState) (θ : ℝ) : ℝ :=
  Real.rpow (Real.sin θ) (halfPower n) * s.g θ

/-- Original `V` represented by the one-dimensional fundamental-theorem
description of `H¹₀(0,π)`.  All conditions refer to the same original `g`.
The `L²` integral is unweighted Lebesgue measure, as in the 2015 source. -/
def AngularEnergyDomain (n : ℕ) (s : AngularState) : Prop :=
  IntervalIntegrable s.scaledDerivative volume (0 : ℝ) Real.pi ∧
  IntervalIntegrable (fun θ : ℝ => (s.scaledDerivative θ) ^ 2)
    volume (0 : ℝ) Real.pi ∧
  (∀ θ ∈ Set.Icc (0 : ℝ) Real.pi,
    scaledFunction n s θ =
      ∫ u in (0 : ℝ)..θ, s.scaledDerivative u) ∧
  (∫ u in (0 : ℝ)..Real.pi, s.scaledDerivative u) = 0 ∧
  IntervalIntegrable
    (fun θ : ℝ =>
      (((n : ℝ) - 2) *
        Real.rpow (Real.sin θ) (((n : ℝ) - 4) / 2) * s.g θ) ^ 2)
    volume (0 : ℝ) Real.pi

/-- Weak derivative of the original `g` on the open angular interval,
recovered from the derivative of `sin^((n-2)/2) g`.  Endpoint values are
irrelevant to the interval integral. -/
def angularDerivative (n : ℕ) (s : AngularState) (θ : ℝ) : ℝ :=
  (s.scaledDerivative θ -
    halfPower n * Real.cos θ *
      Real.rpow (Real.sin θ) (halfPower n - 1) * s.g θ) /
    Real.rpow (Real.sin θ) (halfPower n)

/-- The weight `sin^(n-2)(θ) exp(r cos θ)` of the original angular equation. -/
def angularWeight (n : ℕ) (r θ : ℝ) : ℝ :=
  Real.rpow (Real.sin θ) ((n : ℝ) - 2) *
    Real.exp (r * Real.cos θ)

/-- Angular potential in the original first transverse mode. -/
def angularPotential (n : ℕ) (θ : ℝ) : ℝ :=
  ((n : ℝ) - 2) / (Real.sin θ) ^ 2

/-- The actual original weighted energy bilinear form. -/
def originalWeakForm (n : ℕ) (r : ℝ)
    (s v : AngularState) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    angularWeight n r θ *
      (angularDerivative n s θ * angularDerivative n v θ +
        angularPotential n θ * s.g θ * v.g θ)

/-- Pairing with the original source `sin θ`. -/
def originalSourcePairing (n : ℕ) (r : ℝ)
    (v : AngularState) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    angularWeight n r θ * Real.sin θ * v.g θ

/-- Original angular weak solution, tested against its original energy
space; integrability is explicit to avoid totalized integrals hiding failure. -/
def OriginalWeakGCISolution (n : ℕ) (r : ℝ) (s : AngularState) : Prop :=
  AngularEnergyDomain n s ∧
  ∀ v : AngularState, AngularEnergyDomain n v →
    IntervalIntegrable
      (fun θ : ℝ => angularWeight n r θ *
        (angularDerivative n s θ * angularDerivative n v θ +
          angularPotential n θ * s.g θ * v.g θ))
      volume (0 : ℝ) Real.pi ∧
    IntervalIntegrable
      (fun θ : ℝ => angularWeight n r θ * Real.sin θ * v.g θ)
      volume (0 : ℝ) Real.pi ∧
    originalWeakForm n r s v = originalSourcePairing n r v

/-- Original angular denominator after substituting `h(cos θ)=g(θ)/sin θ`
into DFL's hydrodynamic coefficient. -/
def originalGCIDenominator (n : ℕ) (r : ℝ)
    (s : AngularState) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    s.g θ * Real.exp (r * Real.cos θ) *
      Real.rpow (Real.sin θ) ((n : ℝ) - 1)

/-- Original angular numerator, with exactly one factor `cos θ`. -/
def originalGCINumerator (n : ℕ) (r : ℝ)
    (s : AngularState) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    Real.cos θ * s.g θ * Real.exp (r * Real.cos θ) *
      Real.rpow (Real.sin θ) ((n : ℝ) - 1)

/-- The original GCI coefficient for a solution `g`, not for an arbitrary
one-dimensional amplitude. -/
def originalGCICoefficient (n : ℕ) (r : ℝ)
    (s : AngularState) : ℝ :=
  originalGCINumerator n r s / originalGCIDenominator n r s

/-- Full formal target package: existence of a source weak solution,
independence of the coefficient from the representative/solution, positive
denominator, and the original 2015 comparison.  Only a definition. -/
def DFL2015GCIComparison : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ r : ℝ, 0 < r →
    ∃ s : AngularState,
      OriginalWeakGCISolution n r s ∧
      (∀ v : AngularState, OriginalWeakGCISolution n r v →
        originalGCICoefficient n r v = originalGCICoefficient n r s) ∧
      0 < originalGCIDenominator n r s ∧
      0 < originalGCICoefficient n r s ∧
      originalGCICoefficient n r s < DFL.orientationMean n r

end

end DFL.GCI
