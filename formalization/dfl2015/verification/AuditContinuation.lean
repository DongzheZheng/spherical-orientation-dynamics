import DFL.GCI.ComparisonAll
import DFL.GCI.OriginalUniquenessAll
import DFL.Spectral.ClosedFormHilbertBridges
import DFL.Spectral.GroundHF
import DFL.Spectral.EigenbranchParameter
import DFL.Spectral.PhysicalLatitudeCore
import DFL.GCI.WeakDerivativePrimitive
import DFL.Spectral.GroundConcavity
import DFL.Spectral.RadialPartner
import DFL.GCI.ClassicalEnergyDomainBridge
import DFL.GCI.ClassicalComparisonAll
import DFL.Spectral.PhysicalTransverseCore

/-! Root interfaces added while completing the original proofs,
2026-09-29. Full statements and standard-axiom dependency surfaces. -/

#check DFL.GCI.graphState_mem_energy
#print axioms DFL.GCI.graphState_mem_energy
#check DFL.GCI.stateGraphAmbient_mem
#print axioms DFL.GCI.stateGraphAmbient_mem
#check DFL.GCI.original_weak_GCI_exists_all
#print axioms DFL.GCI.original_weak_GCI_exists_all
#check DFL.GCI.weak_solution_g_unique_ge_three
#print axioms DFL.GCI.weak_solution_g_unique_ge_three
#check DFL.GCI.weak_solution_g_unique_all
#print axioms DFL.GCI.weak_solution_g_unique_all
#check DFL.GCI.weak_solution_scaledDerivative_unique_ge_three
#print axioms DFL.GCI.weak_solution_scaledDerivative_unique_ge_three
#check DFL.GCI.weak_solution_strict_spectral_gap_ge_three
#print axioms DFL.GCI.weak_solution_strict_spectral_gap_ge_three
#check DFL.GCI.original_GCI_positive_all
#print axioms DFL.GCI.original_GCI_positive_all
#check DFL.GCI.dfl2015_gci_comparison
#print axioms DFL.GCI.dfl2015_gci_comparison
#check DFL.GCI.original_GCI_all_strict_shift_chain
#print axioms DFL.GCI.original_GCI_all_strict_shift_chain
#check DFL.GCI.ae_eq_constant_add_primitive_of_weak_derivative
#print axioms DFL.GCI.ae_eq_constant_add_primitive_of_weak_derivative
#check DFL.GCI.classicalH10Graph_eq_primitiveGraph
#print axioms DFL.GCI.classicalH10Graph_eq_primitiveGraph
#check DFL.GCI.angularEnergyDomain_iff_classicalH10_potential
#print axioms DFL.GCI.angularEnergyDomain_iff_classicalH10_potential
#check DFL.GCI.angularEnergyDomain_iff_classicalH10_singular
#print axioms DFL.GCI.angularEnergyDomain_iff_classicalH10_singular
#check DFL.GCI.original_GCI_all_classicalH10_strict_shift_chain
#print axioms DFL.GCI.original_GCI_all_classicalH10_strict_shift_chain
#check DFL.GCI.original_GCI_all_physical_sphere_comparison
#print axioms DFL.GCI.original_GCI_all_physical_sphere_comparison
#check DFL.Spectral.hilbertFormGap_eq_coreGap
#print axioms DFL.Spectral.hilbertFormGap_eq_coreGap
#check DFL.Spectral.formValue_orthogonal_constants
#print axioms DFL.Spectral.formValue_orthogonal_constants
#check DFL.Spectral.positive_latitude_eigenfunction_deriv_neg
#print axioms DFL.Spectral.positive_latitude_eigenfunction_deriv_neg
#check DFL.Spectral.latitude_weight_flux_identity
#print axioms DFL.Spectral.latitude_weight_flux_identity
#check DFL.Spectral.latitude_HF_equality
#print axioms DFL.Spectral.latitude_HF_equality
#check DFL.Spectral.latitude_eigenpair_parameter_derivative_pos
#print axioms DFL.Spectral.latitude_eigenpair_parameter_derivative_pos
#check DFL.Spectral.halfDensity_parameter_equation_of_eigenbranch
#print axioms DFL.Spectral.halfDensity_parameter_equation_of_eigenbranch
#check DFL.Spectral.actual_eigenbranch_derivative_pos
#print axioms DFL.Spectral.actual_eigenbranch_derivative_pos
#check DFL.Spectral.aligned_latitude_integral
#print axioms DFL.Spectral.aligned_latitude_integral
#check DFL.Spectral.latitudeCore_energy_integral
#print axioms DFL.Spectral.latitudeCore_energy_integral
#check DFL.Spectral.tilt_rayleigh_equality_stationary
#print axioms DFL.Spectral.tilt_rayleigh_equality_stationary
#check DFL.Spectral.tilt_ground_energy_strict_concave
#print axioms DFL.Spectral.tilt_ground_energy_strict_concave
#check DFL.Spectral.tilt_ground_energy_even
#print axioms DFL.Spectral.tilt_ground_energy_even
#check DFL.Spectral.original_radial_transverse_ground_ordering
#print axioms DFL.Spectral.original_radial_transverse_ground_ordering
#check DFL.Spectral.radial_derivative_adjoint
#print axioms DFL.Spectral.radial_derivative_adjoint
#check DFL.Spectral.radial_eigenfunction_derivative_partner
#print axioms DFL.Spectral.radial_eigenfunction_derivative_partner
#check DFL.Spectral.partner_eigenfunction_recovers_radial
#print axioms DFL.Spectral.partner_eigenfunction_recovers_radial
#check DFL.Spectral.radial_recover_derivative_eigenfunction
#print axioms DFL.Spectral.radial_recover_derivative_eigenfunction
#check DFL.Spectral.radial_adjoint_green_identity
#print axioms DFL.Spectral.radial_adjoint_green_identity
#check DFL.Spectral.radial_recover_weighted_mean_zero
#print axioms DFL.Spectral.radial_recover_weighted_mean_zero
#check DFL.Spectral.transverseCore_energy_integral
#print axioms DFL.Spectral.transverseCore_energy_integral
#check DFL.Spectral.transverseCore_norm_amplitude_integral
#print axioms DFL.Spectral.transverseCore_norm_amplitude_integral
