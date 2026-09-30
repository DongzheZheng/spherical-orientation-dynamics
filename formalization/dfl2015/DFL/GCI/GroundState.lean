import DFL.GCI.AngularEnergy

/-!
# Exact positive supersolution for the actual GCI amplitude operator

For the 2015 paper's ambient dimension `n`, the transformed amplitude
operator acts on the auxiliary sphere of dimension `n+1`.  This file checks
the explicit positive function used in the JPhysA proof.  It supplies the
coercive potential calculation, while existence and positivity of the
original weak solution still require a separate elliptic argument.
-/

namespace DFL.GCI

noncomputable section

/-- The actual GCI amplitude differential expression in ambient dimension
`n`: `-w h'' + ((n+1)t-rw)h' + (n-1+rt)h`. -/
def amplitudeOperatorValue (n : ℕ) (r t f fp fpp : ℝ) : ℝ :=
  -(1 - t ^ 2) * fpp +
    (((n : ℝ) + 1) * t - r * (1 - t ^ 2)) * fp +
    (((n : ℝ) - 1) + r * t) * f

/-- Positive factor `exp(-rt/(n+1))` from the paper's ground-state
transformation. -/
def groundFactor (n : ℕ) (r t : ℝ) : ℝ :=
  Real.exp (-(r / ((n : ℝ) + 1)) * t)

theorem groundFactor_pos (n : ℕ) (r t : ℝ) :
    0 < groundFactor n r t := by
  unfold groundFactor
  positivity

theorem groundFactor_hasDerivAt (n : ℕ) (r t : ℝ) :
    HasDerivAt (groundFactor n r)
      (-(r / ((n : ℝ) + 1)) * groundFactor n r t) t := by
  unfold groundFactor
  have hlin : HasDerivAt
      (fun s : ℝ => -(r / ((n : ℝ) + 1)) * s)
      (-(r / ((n : ℝ) + 1))) t := by
    convert (hasDerivAt_id t).const_mul (-(r / ((n : ℝ) + 1))) using 1; ring
  convert (Real.hasDerivAt_exp _).comp t hlin using 1; ring

theorem groundFactor_deriv (n : ℕ) (r t : ℝ) :
    deriv (groundFactor n r) t =
      -(r / ((n : ℝ) + 1)) * groundFactor n r t :=
  (groundFactor_hasDerivAt n r t).deriv

theorem groundFactor_second_deriv (n : ℕ) (r t : ℝ) :
    deriv (deriv (groundFactor n r)) t =
      (r / ((n : ℝ) + 1)) ^ 2 * groundFactor n r t := by
  have hfun : deriv (groundFactor n r) =
      fun s : ℝ => -(r / ((n : ℝ) + 1)) * groundFactor n r s := by
    funext s
    exact groundFactor_deriv n r s
  rw [hfun]
  convert ((groundFactor_hasDerivAt n r t).const_mul
    (-(r / ((n : ℝ) + 1)))).deriv using 1; ring

/-- The exact algebraic quotient `Lφ/φ`; the `rt` terms cancel. -/
theorem ground_operator_quotient (n : ℕ) (r t : ℝ) :
    amplitudeOperatorValue n r t 1
      (-(r / ((n : ℝ) + 1)))
      ((r / ((n : ℝ) + 1)) ^ 2) =
    ((n : ℝ) - 1) +
      ((n : ℝ) / (((n : ℝ) + 1) ^ 2)) * r ^ 2 * (1 - t ^ 2) := by
  have hne : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold amplitudeOperatorValue
  field_simp
  ring

/-- At every physical concentration and coordinate, the ground-state
potential is at least `n-1 > 0`. -/
theorem ground_operator_quotient_ge (n : ℕ)
    (r t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    ((n : ℝ) - 1) ≤
      amplitudeOperatorValue n r t 1
        (-(r / ((n : ℝ) + 1)))
        ((r / ((n : ℝ) + 1)) ^ 2) := by
  rw [ground_operator_quotient]
  have hnr : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hw : 0 ≤ 1 - t ^ 2 := by
    have hp : 0 ≤ (1 - t) * (1 + t) :=
      mul_nonneg (by linarith [ht.2]) (by linarith [ht.1])
    nlinarith
  have hden : 0 ≤ (n : ℝ) / (((n : ℝ) + 1) ^ 2) :=
    div_nonneg hnr (sq_nonneg _)
  nlinarith [mul_nonneg (mul_nonneg hden (sq_nonneg r)) hw]

theorem ground_operator_quotient_pos (n : ℕ) (hn : 2 ≤ n)
    (r t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 < amplitudeOperatorValue n r t 1
      (-(r / ((n : ℝ) + 1)))
      ((r / ((n : ℝ) + 1)) ^ 2) := by
  have hnr : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hge := ground_operator_quotient_ge n r t ht
  linarith

/-- The derivative calculations and polynomial identity combine to verify
the true differential expression on the positive `groundFactor`. -/
theorem amplitudeOperator_groundFactor (n : ℕ) (r t : ℝ) :
    amplitudeOperatorValue n r t
      (groundFactor n r t)
      (deriv (groundFactor n r) t)
      (deriv (deriv (groundFactor n r)) t) =
    groundFactor n r t *
      (((n : ℝ) - 1) +
        ((n : ℝ) / (((n : ℝ) + 1) ^ 2)) * r ^ 2 * (1 - t ^ 2)) := by
  rw [groundFactor_deriv, groundFactor_second_deriv]
  have hfactor :
      amplitudeOperatorValue n r t
          (groundFactor n r t)
          (-(r / ((n : ℝ) + 1)) * groundFactor n r t)
          ((r / ((n : ℝ) + 1)) ^ 2 * groundFactor n r t) =
        groundFactor n r t *
          amplitudeOperatorValue n r t 1
            (-(r / ((n : ℝ) + 1)))
            ((r / ((n : ℝ) + 1)) ^ 2) := by
    unfold amplitudeOperatorValue
    ring
  rw [hfactor, ground_operator_quotient]

end

end DFL.GCI
