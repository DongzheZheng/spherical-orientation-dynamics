import DFL.GCI.DerivativeEquation
import DFL.GCI.ComparisonTwoD
import DFL.GCI.ComparisonFourUpper
import DFL.GCI.ComparisonGenericUpper

/-! Target/validity audit.  The `DFL2015GCIComparison` line is a `Prop`
declaration only, not a theorem. -/

#check DFL.GCI.DFL2015GCIComparison
#check DFL.GCI.OriginalWeakGCISolution
#check DFL.GCI.weak_solution_denominator_nonneg
#check DFL.GCI.amplitudeOperator_groundFactor
#check DFL.GCI.derivative_equation_of_poisson
#check DFL.GCI.derivativeOperator_groundFactor
#check DFL.GCI.derivativeGround_operator_quotient_pos
#check DFL.GCI.positiveTestState_mem_energy
#check DFL.GCI.positiveTest_self_energy_integrable
#check DFL.GCI.weak_solution_denominator_pos
#check DFL.GCI.sineTestState_mem_energy
#check DFL.GCI.weak_solution_moment_identity_twoD
#check DFL.GCI.weak_solution_mass_lt_denominator_twoD
#check DFL.GCI.weak_solution_numerator_pos_twoD
#check DFL.GCI.weak_solution_coefficient_pos_twoD
#check DFL.GCI.twoDSineEnergy_eq_forcingNorm_add_shiftMoment
#check DFL.GCI.weak_solution_energy_cauchy_twoD
#check DFL.GCI.weak_solution_coefficient_le_shift_moment_twoD
#check DFL.GCI.explicit_original_weak_solution_twoD
#check DFL.GCI.weak_solution_g_unique_twoD
#check DFL.GCI.original_GCI_twoD_exists_unique_positive
#check DFL.GCI.weak_solution_GCI_comparison_twoD
#check DFL.GCI.original_GCI_twoD_full_comparison
#check DFL.GCI.weak_solution_energy_cauchy
#check DFL.GCI.weak_solution_forcing_energy_cauchy
#check DFL.GCI.sineTest_self_energy_eq_forcing_add_shift
#check DFL.GCI.orientationMean_shift_eq_angular_shift_ratio
#check DFL.GCI.weak_solution_moment_identity_fourD
#check DFL.GCI.weak_solution_coefficient_lt_orientation_fourD
#check DFL.GCI.weak_solution_coefficient_lt_orientation_of_moment

#print axioms DFL.GCI.weak_solution_denominator_nonneg
#print axioms DFL.GCI.amplitudeOperator_groundFactor
#print axioms DFL.GCI.derivative_equation_of_poisson
#print axioms DFL.GCI.derivativeOperator_groundFactor
#print axioms DFL.GCI.derivativeGround_operator_quotient_pos
#print axioms DFL.GCI.positiveTestState_mem_energy
#print axioms DFL.GCI.positiveTest_self_energy_integrable
#print axioms DFL.GCI.weak_solution_denominator_pos
#print axioms DFL.GCI.sineTestState_mem_energy
#print axioms DFL.GCI.weak_solution_moment_identity_twoD
#print axioms DFL.GCI.weak_solution_mass_lt_denominator_twoD
#print axioms DFL.GCI.weak_solution_numerator_pos_twoD
#print axioms DFL.GCI.weak_solution_coefficient_pos_twoD
#print axioms DFL.GCI.twoDSineEnergy_eq_forcingNorm_add_shiftMoment
#print axioms DFL.GCI.weak_solution_energy_cauchy_twoD
#print axioms DFL.GCI.weak_solution_coefficient_le_shift_moment_twoD
#print axioms DFL.GCI.explicit_original_weak_solution_twoD
#print axioms DFL.GCI.weak_solution_g_unique_twoD
#print axioms DFL.GCI.original_GCI_twoD_exists_unique_positive
#print axioms DFL.GCI.weak_solution_GCI_comparison_twoD
#print axioms DFL.GCI.original_GCI_twoD_full_comparison
#print axioms DFL.GCI.weak_solution_energy_cauchy
#print axioms DFL.GCI.weak_solution_forcing_energy_cauchy
#print axioms DFL.GCI.sineTest_self_energy_eq_forcing_add_shift
#print axioms DFL.GCI.orientationMean_shift_eq_angular_shift_ratio
#print axioms DFL.GCI.weak_solution_moment_identity_fourD
#print axioms DFL.GCI.weak_solution_coefficient_lt_orientation_fourD
#print axioms DFL.GCI.weak_solution_coefficient_lt_orientation_of_moment
