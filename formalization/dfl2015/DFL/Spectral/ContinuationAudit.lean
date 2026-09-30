import DFL.Spectral.ClosedFormHilbertBridges
import DFL.Spectral.PhysicalModeDerivatives
import DFL.Spectral.PhysicalLatitudeCore

#print axioms DFL.Spectral.hilbertFormSpace_complete
#print axioms DFL.Spectral.hilbertFormGap_eq_coreGap
#print axioms DFL.Spectral.formValue_orthogonal_constants
#print axioms DFL.Spectral.positive_latitude_eigenfunction_deriv_neg
#print axioms DFL.Spectral.latitude_weight_flux_identity
#print axioms DFL.Spectral.halfDensity_green_identity
#print axioms DFL.Spectral.halfDensity_HF_integral
#print axioms DFL.Spectral.halfDensityApply_lift
#print axioms DFL.Spectral.latitude_HF_equality
#print axioms DFL.Spectral.latitude_eigenpair_parameter_derivative_pos
#print axioms DFL.Spectral.physical_angular_eigenpair_derivative_pos
#print axioms DFL.Spectral.physical_radial_partner_eigenpair_derivative_pos
#print axioms DFL.Spectral.latitudeCore_tangentGradient
#print axioms DFL.Spectral.aligned_latitude_integral
#print axioms DFL.Spectral.latitudeCore_energy_integral

#synth InnerProductSpace ℝ (DFL.Spectral.HilbertFormSpace 2 1)
#synth CompleteSpace (DFL.Spectral.HilbertFormSpace 2 1)

