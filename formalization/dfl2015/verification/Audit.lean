import DFL

/-! Server-only declaration and axiom audit.  This file prints the statement
target and the dependency surfaces of the selected proved interfaces. -/

#check DFL.DFL2015UnimodalityConjecture
#print DFL.IsUnimodal
#print DFL.DFL2015UnimodalityConjecture
#check DFL.Probability.strict_reverse_covariance
#print axioms DFL.Probability.strict_reverse_covariance
#check DFL.Probability.strict_reverse_covariance_of_strictAntiOn
#print axioms DFL.Probability.strict_reverse_covariance_of_strictAntiOn
#check DFL.Probability.energy_response_pos_of_positive_test
#print axioms DFL.Probability.energy_response_pos_of_positive_test
#check DFL.Probability.picone_integral_identity_ac
#print axioms DFL.Probability.picone_integral_identity_ac
#check DFL.Probability.Ioi_zero_eq_of_positive_tails
#print axioms DFL.Probability.Ioi_zero_eq_of_positive_tails

#check DFL.Hysteresis.inverseFeedback_spec
#print axioms DFL.Hysteresis.inverseFeedback_spec
#check DFL.Hysteresis.inverseFeedback_pos
#print axioms DFL.Hysteresis.inverseFeedback_pos
#check DFL.Hysteresis.inverseFeedback_elasticity
#print axioms DFL.Hysteresis.inverseFeedback_elasticity
#check DFL.Hysteresis.densityCurve_sign
#print axioms DFL.Hysteresis.densityCurve_sign
#check DFL.Hysteresis.original_curve_log_deriv
#print axioms DFL.Hysteresis.original_curve_log_deriv
#check DFL.Hysteresis.equilibriumDensity_pos
#print axioms DFL.Hysteresis.equilibriumDensity_pos
#check DFL.Hysteresis.original_curve_positive_slope_iff
#print axioms DFL.Hysteresis.original_curve_positive_slope_iff

#check DFL.marginalWeight_intervalIntegrable
#print axioms DFL.marginalWeight_intervalIntegrable
#check DFL.firstMoment_intervalIntegrable
#print axioms DFL.firstMoment_intervalIntegrable
#check DFL.partition_pos
#print axioms DFL.partition_pos
#check DFL.firstMoment_pos
#print axioms DFL.firstMoment_pos
#check DFL.partition_hasDerivAt_firstMoment
#print axioms DFL.partition_hasDerivAt_firstMoment
#check DFL.firstMoment_hasDerivAt_secondMoment
#print axioms DFL.firstMoment_hasDerivAt_secondMoment
#check DFL.marginalWellDefined
#print axioms DFL.marginalWellDefined
#check DFL.secondMoment_intervalIntegrable
#print axioms DFL.secondMoment_intervalIntegrable
#check DFL.moment_recurrence
#print axioms DFL.moment_recurrence
#check DFL.orientationMean_riccati
#print axioms DFL.orientationMean_riccati
#check DFL.orientationMean_elasticity_ode
#print axioms DFL.orientationMean_elasticity_ode
#check DFL.firstMoment_zero
#print axioms DFL.firstMoment_zero
#check DFL.orientationMean_lt_one
#print axioms DFL.orientationMean_lt_one
#check DFL.orientationMean_tendsto_one_atTop
#print axioms DFL.orientationMean_tendsto_one_atTop
#check DFL.equilibriumDensity_tendsto_atTop
#print axioms DFL.equilibriumDensity_tendsto_atTop
#check DFL.zero_field_second_moment
#print axioms DFL.zero_field_second_moment
#check DFL.orientationMean_div_tendsto_zero_right
#print axioms DFL.orientationMean_div_tendsto_zero_right
#check DFL.Hysteresis.DimensionShift.orientationMean_dimension_shift
#print axioms DFL.Hysteresis.DimensionShift.orientationMean_dimension_shift
#check DFL.endpointAtZero
#print axioms DFL.endpointAtZero
#check DFL.orientationMean_deriv_of_moment_derivs
#print axioms DFL.orientationMean_deriv_of_moment_derivs
#check DFL.Hysteresis.ElasticityODE.elasticity_ode
#print axioms DFL.Hysteresis.ElasticityODE.elasticity_ode

#check DFL.Hysteresis.PositiveRoot.root_gt_test
#print axioms DFL.Hysteresis.PositiveRoot.root_gt_test
#check DFL.Hysteresis.ZeroDirection.existsUnique_q_eq_one
#print axioms DFL.Hysteresis.ZeroDirection.existsUnique_q_eq_one
#check DFL.Hysteresis.ZeroDirectionBridge.thresholdRatio_scaled
#print axioms DFL.Hysteresis.ZeroDirectionBridge.thresholdRatio_scaled
#check DFL.Hysteresis.ZeroDirectionODE.r_mul_F_zero
#print axioms DFL.Hysteresis.ZeroDirectionODE.r_mul_F_zero
#check DFL.Hysteresis.ZeroDirectionODE.existsUnique_zero_direction
#print axioms DFL.Hysteresis.ZeroDirectionODE.existsUnique_zero_direction
#check DFL.Hysteresis.OriginalTrajectory.original_scaledMean_eq_Y
#print axioms DFL.Hysteresis.OriginalTrajectory.original_scaledMean_eq_Y
#check DFL.Hysteresis.OriginalTrajectory.original_H_ode
#print axioms DFL.Hysteresis.OriginalTrajectory.original_H_ode
#check DFL.Hysteresis.OriginalTrajectory.original_density_slope
#print axioms DFL.Hysteresis.OriginalTrajectory.original_density_slope
#check DFL.Hysteresis.original_H_positive_arbitrarily_late
#print axioms DFL.Hysteresis.original_H_positive_arbitrarily_late
#check DFL.Hysteresis.ZeroDirectionOnTrajectory.exists_original_H_zero_direction
#print axioms DFL.Hysteresis.ZeroDirectionOnTrajectory.exists_original_H_zero_direction
#check DFL.Hysteresis.isUnimodal_of_original_H_signs
#print axioms DFL.Hysteresis.isUnimodal_of_original_H_signs
#check DFL.Hysteresis.MeanLinearBound.orientationMean_lt_linear
#print axioms DFL.Hysteresis.MeanLinearBound.orientationMean_lt_linear
#check DFL.Hysteresis.SmallFieldSign.original_H_neg_small
#print axioms DFL.Hysteresis.SmallFieldSign.original_H_neg_small
#check DFL.Hysteresis.OriginalCrossing.crossing_of_small_negative
#print axioms DFL.Hysteresis.OriginalCrossing.crossing_of_small_negative
#check DFL.dfl2015_unimodality_formula
#print axioms DFL.dfl2015_unimodality_formula
#check DFL.Hysteresis.original_nondegenerateFold
#print axioms DFL.Hysteresis.original_nondegenerateFold
#check DFL.Hysteresis.Crossing.crossing_from_derivative_signs
#print axioms DFL.Hysteresis.Crossing.crossing_from_derivative_signs
#check DFL.Geometry.spherePartition_pos
#print axioms DFL.Geometry.spherePartition_pos
#check DFL.Geometry.sphereOrientationMean_eq_of_moment_bridge
#print axioms DFL.Geometry.sphereOrientationMean_eq_of_moment_bridge
#check DFL.Geometry.sphere_isUnimodal_of_moment_bridge
#print axioms DFL.Geometry.sphere_isUnimodal_of_moment_bridge
#check DFL.Geometry.coordinateLaw_three_eq_smul_volume
#print axioms DFL.Geometry.coordinateLaw_three_eq_smul_volume
#check DFL.Geometry.sphereMomentBridge_three
#print axioms DFL.Geometry.sphereMomentBridge_three
#check DFL.Geometry.sphere_isUnimodal_three
#print axioms DFL.Geometry.sphere_isUnimodal_three
#check DFL.Geometry.sphere_nondegenerateFold_three
#print axioms DFL.Geometry.sphere_nondegenerateFold_three
#check DFL.Geometry.coordinateLaw_two_eq_two_smul_measureT
#print axioms DFL.Geometry.coordinateLaw_two_eq_two_smul_measureT
#check DFL.Geometry.sphereMomentBridge_two
#print axioms DFL.Geometry.sphereMomentBridge_two
#check DFL.Geometry.sphere_isUnimodal_two
#print axioms DFL.Geometry.sphere_isUnimodal_two
#check DFL.Geometry.sphere_nondegenerateFold_two
#print axioms DFL.Geometry.sphere_nondegenerateFold_two
#check DFL.Geometry.coordinateLaw_succ_eq_smul_beta
#print axioms DFL.Geometry.coordinateLaw_succ_eq_smul_beta
#check DFL.Geometry.sphereMomentBridge_all
#print axioms DFL.Geometry.sphereMomentBridge_all
#check DFL.Geometry.sphere_isUnimodal_all
#print axioms DFL.Geometry.sphere_isUnimodal_all
#check DFL.Geometry.sphere_nondegenerateFold_all
#print axioms DFL.Geometry.sphere_nondegenerateFold_all
#check DFL.GCI.weak_solution_denominator_pos
#print axioms DFL.GCI.weak_solution_denominator_pos
#check DFL.GCI.weak_solution_moment_identity_twoD
#print axioms DFL.GCI.weak_solution_moment_identity_twoD
#check DFL.GCI.explicit_original_weak_solution_twoD
#print axioms DFL.GCI.explicit_original_weak_solution_twoD
#check DFL.GCI.weak_solution_coefficient_unique_twoD
#print axioms DFL.GCI.weak_solution_coefficient_unique_twoD
#check DFL.GCI.weak_solution_coefficient_pos_twoD
#print axioms DFL.GCI.weak_solution_coefficient_pos_twoD
#check DFL.GCI.orientationMean_four_eq_twoD_shift_ratio
#print axioms DFL.GCI.orientationMean_four_eq_twoD_shift_ratio
#check DFL.GCI.original_GCI_twoD_full_comparison
#print axioms DFL.GCI.original_GCI_twoD_full_comparison
#check DFL.GCI.original_GCI_twoD_physical_circle_comparison
#print axioms DFL.GCI.original_GCI_twoD_physical_circle_comparison
#check DFL.GCI.weak_solution_coefficient_lt_shift_mean_twoD
#print axioms DFL.GCI.weak_solution_coefficient_lt_shift_mean_twoD
#check DFL.GCI.original_GCI_twoD_strict_shift_chain
#print axioms DFL.GCI.original_GCI_twoD_strict_shift_chain
#check DFL.GCI.originalForcingNorm_eq_shifted_partition
#print axioms DFL.GCI.originalForcingNorm_eq_shifted_partition
#check DFL.GCI.originalShiftMoment_eq_shifted_firstMoment
#print axioms DFL.GCI.originalShiftMoment_eq_shifted_firstMoment
#check DFL.GCI.weak_solution_forcing_energy_cauchy
#print axioms DFL.GCI.weak_solution_forcing_energy_cauchy
#check DFL.GCI.weak_solution_moment_identity_fourD
#print axioms DFL.GCI.weak_solution_moment_identity_fourD
#check DFL.GCI.weak_solution_coefficient_lt_orientation_fourD
#print axioms DFL.GCI.weak_solution_coefficient_lt_orientation_fourD
#check DFL.GCI.weak_solution_coefficient_lt_orientation_of_moment
#print axioms DFL.GCI.weak_solution_coefficient_lt_orientation_of_moment
#check DFL.GCI.weak_solution_moment_identity_ge_four
#print axioms DFL.GCI.weak_solution_moment_identity_ge_four
#check DFL.GCI.original_GCI_strict_upper_ge_four
#print axioms DFL.GCI.original_GCI_strict_upper_ge_four
#check DFL.GCI.weak_solution_moment_identity_all
#print axioms DFL.GCI.weak_solution_moment_identity_all
#check DFL.GCI.original_GCI_shift_upper_all
#print axioms DFL.GCI.original_GCI_shift_upper_all
#check DFL.GCI.original_GCI_strict_upper_all
#print axioms DFL.GCI.original_GCI_strict_upper_all
#check DFL.GCI.weak_solution_denominator_unique_all
#print axioms DFL.GCI.weak_solution_denominator_unique_all
#check DFL.GCI.weak_solution_numerator_unique_all
#print axioms DFL.GCI.weak_solution_numerator_unique_all
#check DFL.GCI.weak_solution_coefficient_unique_all
#print axioms DFL.GCI.weak_solution_coefficient_unique_all
#check DFL.GCI.weak_solution_weighted_mass_cauchy_threeD
#print axioms DFL.GCI.weak_solution_weighted_mass_cauchy_threeD
#check DFL.GCI.weak_solution_numerator_pos_three_of_spectral_gap
#print axioms DFL.GCI.weak_solution_numerator_pos_three_of_spectral_gap
#check DFL.Spectral.alignedMeasure_probability
#print axioms DFL.Spectral.alignedMeasure_probability
#check DFL.Spectral.sphereVariance_pos_iff_not_ae_constant
#print axioms DFL.Spectral.sphereVariance_pos_iff_not_ae_constant
#check DFL.Spectral.transverseCoordinateTrialRatio_eq
#print axioms DFL.Spectral.transverseCoordinateTrialRatio_eq
#check DFL.Spectral.alignedMeasure_bounds
#print axioms DFL.Spectral.alignedMeasure_bounds
#check DFL.Spectral.coreFormNormSq_bounds
#print axioms DFL.Spectral.coreFormNormSq_bounds
#check DFL.Spectral.coreGap_zero_le_dimension
#print axioms DFL.Spectral.coreGap_zero_le_dimension
#check DFL.Spectral.coreGap_field_lower
#print axioms DFL.Spectral.coreGap_field_lower
#check DFL.Spectral.closedFormSpace_complete
#print axioms DFL.Spectral.closedFormSpace_complete
#check DFL.Spectral.coreGraph_value_norm_sq
#print axioms DFL.Spectral.coreGraph_value_norm_sq
#check DFL.Spectral.coreGraph_gradient_norm_sq
#print axioms DFL.Spectral.coreGraph_gradient_norm_sq
#check DFL.Spectral.closedFormGap_eq_coreGap
#print axioms DFL.Spectral.closedFormGap_eq_coreGap
