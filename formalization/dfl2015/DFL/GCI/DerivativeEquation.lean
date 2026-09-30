import DFL.GCI.GroundState

/-!
# Differentiating the actual GCI amplitude equation

This is the algebraic and calculus step behind `D_r h' = -r h` in the
JPhysA manuscript.  It does not supply a solution of `L_r h = 1` or
identify that solution with the original angular weak solution.
-/

namespace DFL.GCI

noncomputable section

/-- The operator acting on `h'` after differentiating the original GCI
amplitude equation in ambient dimension `n`. -/
def derivativeOperatorValue (n : ℕ) (r t fp fpp fppp : ℝ) : ℝ :=
  -(1 - t ^ 2) * fppp +
    (((n : ℝ) + 3) * t - r * (1 - t ^ 2)) * fpp +
    ((2 * (n : ℝ)) + 3 * r * t) * fp

/-- Exact derivative of the original amplitude differential expression,
under only the displayed local derivative hypotheses. -/
theorem amplitudeOperator_hasDerivAt
    (n : ℕ) (r t : ℝ) (h0 h1 h2 h3 : ℝ → ℝ)
    (hd0 : HasDerivAt h0 (h1 t) t)
    (hd1 : HasDerivAt h1 (h2 t) t)
    (hd2 : HasDerivAt h2 (h3 t) t) :
    HasDerivAt
      (fun s => amplitudeOperatorValue n r s (h0 s) (h1 s) (h2 s))
      (derivativeOperatorValue n r t (h1 t) (h2 t) (h3 t) + r * h0 t)
      t := by
  have hw : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-2 * t) t := by
    convert ((hasDerivAt_id t).pow 2).const_sub (1 : ℝ) using 1
    simp only [id_eq]
    ring
  have hminusw : HasDerivAt (fun s : ℝ => -(1 - s ^ 2)) (2 * t) t := by
    convert hw.neg using 1; ring
  have hdrift : HasDerivAt
      (fun s : ℝ => ((n : ℝ) + 1) * s - r * (1 - s ^ 2))
      (((n : ℝ) + 1) + 2 * r * t) t := by
    convert (((hasDerivAt_id t).const_mul ((n : ℝ) + 1)).sub
      (hw.const_mul r)) using 1
    ring
  have hpot : HasDerivAt
      (fun s : ℝ => ((n : ℝ) - 1) + r * s) r t := by
    convert ((hasDerivAt_id t).const_mul r).const_add ((n : ℝ) - 1) using 1; ring
  have hmain :=
    (hminusw.mul hd2).add ((hdrift.mul hd1).add (hpot.mul hd0))
  convert hmain using 1
  · funext s
    dsimp [amplitudeOperatorValue]
    ring
  · dsimp [derivativeOperatorValue]
    ring

/-- If the actual amplitude equation `L_r h = 1` holds and `h` has the
displayed derivatives, then its derivative satisfies exactly the equation
used for monotonicity: `D_r h' = -r h`. -/
theorem derivative_equation_of_poisson
    (n : ℕ) (r t : ℝ) (h0 h1 h2 h3 : ℝ → ℝ)
    (hd0 : HasDerivAt h0 (h1 t) t)
    (hd1 : HasDerivAt h1 (h2 t) t)
    (hd2 : HasDerivAt h2 (h3 t) t)
    (hpoisson : ∀ s : ℝ,
      amplitudeOperatorValue n r s (h0 s) (h1 s) (h2 s) = 1) :
    derivativeOperatorValue n r t (h1 t) (h2 t) (h3 t) = -r * h0 t := by
  have hderiv := amplitudeOperator_hasDerivAt n r t h0 h1 h2 h3 hd0 hd1 hd2
  have hfun :
      (fun s => amplitudeOperatorValue n r s (h0 s) (h1 s) (h2 s)) =
        fun _ : ℝ => (1 : ℝ) := by
    funext s
    exact hpoisson s
  rw [hfun] at hderiv
  have hzero : derivativeOperatorValue n r t (h1 t) (h2 t) (h3 t) +
      r * h0 t = 0 := by
    have h := hderiv.deriv
    simpa only [deriv_const, eq_comm] using h
  linarith

/-- The positive supersolution for the derivative operator `D_r`, with
the source paper's exact coefficient `3r/(n+3)`. -/
def derivativeGroundFactor (n : ℕ) (r t : ℝ) : ℝ :=
  Real.exp (-(3 * r / ((n : ℝ) + 3)) * t)

theorem derivativeGroundFactor_pos (n : ℕ) (r t : ℝ) :
    0 < derivativeGroundFactor n r t := by
  unfold derivativeGroundFactor
  positivity

theorem derivativeGroundFactor_hasDerivAt (n : ℕ) (r t : ℝ) :
    HasDerivAt (derivativeGroundFactor n r)
      (-(3 * r / ((n : ℝ) + 3)) * derivativeGroundFactor n r t) t := by
  unfold derivativeGroundFactor
  have hlin : HasDerivAt
      (fun s : ℝ => -(3 * r / ((n : ℝ) + 3)) * s)
      (-(3 * r / ((n : ℝ) + 3))) t := by
    convert (hasDerivAt_id t).const_mul (-(3 * r / ((n : ℝ) + 3))) using 1; ring
  convert (Real.hasDerivAt_exp _).comp t hlin using 1; ring

theorem derivativeGroundFactor_deriv (n : ℕ) (r t : ℝ) :
    deriv (derivativeGroundFactor n r) t =
      -(3 * r / ((n : ℝ) + 3)) * derivativeGroundFactor n r t :=
  (derivativeGroundFactor_hasDerivAt n r t).deriv

theorem derivativeGroundFactor_second_deriv (n : ℕ) (r t : ℝ) :
    deriv (deriv (derivativeGroundFactor n r)) t =
      (3 * r / ((n : ℝ) + 3)) ^ 2 * derivativeGroundFactor n r t := by
  have hfun : deriv (derivativeGroundFactor n r) =
      fun s : ℝ => -(3 * r / ((n : ℝ) + 3)) * derivativeGroundFactor n r s := by
    funext s
    exact derivativeGroundFactor_deriv n r s
  rw [hfun]
  convert ((derivativeGroundFactor_hasDerivAt n r t).const_mul
    (-(3 * r / ((n : ℝ) + 3)))).deriv using 1; ring

/-- The exact second ground-state quotient:
`D_r φ_D / φ_D = 2n + 3n r²(1-t²)/(n+3)²`. -/
theorem derivativeGround_operator_quotient (n : ℕ) (r t : ℝ) :
    derivativeOperatorValue n r t 1
      (-(3 * r / ((n : ℝ) + 3)))
      ((3 * r / ((n : ℝ) + 3)) ^ 2) =
    2 * (n : ℝ) +
      (3 * (n : ℝ) / (((n : ℝ) + 3) ^ 2)) * r ^ 2 * (1 - t ^ 2) := by
  have hne : (n : ℝ) + 3 ≠ 0 := by positivity
  unfold derivativeOperatorValue
  field_simp
  ring

/-- Actual differential expression on `φ_D`, including its verified
first and second derivatives. -/
theorem derivativeOperator_groundFactor (n : ℕ) (r t : ℝ) :
    derivativeOperatorValue n r t
      (derivativeGroundFactor n r t)
      (deriv (derivativeGroundFactor n r) t)
      (deriv (deriv (derivativeGroundFactor n r)) t) =
    derivativeGroundFactor n r t *
      (2 * (n : ℝ) +
        (3 * (n : ℝ) / (((n : ℝ) + 3) ^ 2)) * r ^ 2 * (1 - t ^ 2)) := by
  rw [derivativeGroundFactor_deriv, derivativeGroundFactor_second_deriv]
  have hfactor :
      derivativeOperatorValue n r t
          (derivativeGroundFactor n r t)
          (-(3 * r / ((n : ℝ) + 3)) * derivativeGroundFactor n r t)
          ((3 * r / ((n : ℝ) + 3)) ^ 2 * derivativeGroundFactor n r t) =
        derivativeGroundFactor n r t *
          derivativeOperatorValue n r t 1
            (-(3 * r / ((n : ℝ) + 3)))
            ((3 * r / ((n : ℝ) + 3)) ^ 2) := by
    unfold derivativeOperatorValue
    ring
  rw [hfactor, derivativeGround_operator_quotient]

theorem derivativeGround_operator_quotient_pos
    (n : ℕ) (hn : 2 ≤ n) (r t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 < derivativeOperatorValue n r t 1
      (-(3 * r / ((n : ℝ) + 3)))
      ((3 * r / ((n : ℝ) + 3)) ^ 2) := by
  rw [derivativeGround_operator_quotient]
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hw : 0 ≤ 1 - t ^ 2 := by
    have hp : 0 ≤ (1 - t) * (1 + t) :=
      mul_nonneg (by linarith [ht.2]) (by linarith [ht.1])
    nlinarith
  have hden : 0 ≤ 3 * (n : ℝ) / (((n : ℝ) + 3) ^ 2) :=
    div_nonneg (by positivity) (sq_nonneg _)
  nlinarith [mul_nonneg (mul_nonneg hden (sq_nonneg r)) hw]

end

end DFL.GCI
