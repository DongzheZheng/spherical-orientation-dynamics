import continuation
import DFLSphere433.Verification
import continuation.PotentialMinimumDependence
import continuation.PotentialRayleighStationarity
import continuation.RoundSphereGroundDomain
import continuation.SmoothAbsoluteH1
import continuation.SmoothSchrodingerPositivity
import continuation.RoundSpherePositiveGround
import continuation.TiltStrictConcavity
import continuation.TiltEvenness
import continuation.EvenSquareProfile
import continuation.RoundSphereLatitudeProfile
import continuation.RoundSphereGroundSymmetry
import continuation.RoundSphereLatitudeOperator
import continuation.RoundSphereGroundAxisymmetry
import continuation.RoundSphereActualTiltProfile
import continuation.OriginalTiltGroundExists
import continuation.OriginalWeightedGround
import continuation.GroundStateContinuity
import continuation.TiltHellmannFeynman
import continuation.SphereGroundMoments
import continuation.SphereStrictMonotonicity
import continuation.WarpedProductVolume
import continuation.PolarRoundMetric
import continuation.SeparatedGradient
import DFLSphere433.OriginalLatitude.EigenbranchParameter
import DFLSphere433.OriginalLatitude.PhysicalModeDerivatives
import DFLSphere433.OriginalLatitude.RadialPartner
import continuation.TiltDriftClassification
import continuation.ProductGradientSlices
import continuation.SeparatedMeasureFubini
import continuation.CotSphereDiffeomorph
import continuation.CotSphereDifferential
import continuation.CotSphereMetric
import continuation.CotSphereVolume
import continuation.SeparatedBochnerFubini
import continuation.CotSphereEnergy
import continuation.CotSphereFullIntegral
import continuation.TiltRateContinuity
import continuation.CotSphereBochnerEnergy
import continuation.RoundCircleSharpGap
import continuation.PhysicalGapIdentification
import continuation.LatMeasureBochner
import continuation.TransverseWeakH1
import continuation.CotAngularEquality
import continuation.OriginalTiltEigenspaceSimple
import continuation.PhysicalFirstDimension
import continuation.CircleFirstDimension
import continuation.WeakFirstEigenspace
import continuation.WeightedWeakH1Gauge
import continuation.OriginalWeightedWeakGap
import continuation.OriginalWeakFirstEquality
import continuation.NormalizedVMFWeakGap
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Kernel dependency audit of every declaration in the actual imported
own-source closure, including all public mathematical statements. The
initial twelve-module audit remains in `DFLSphere433.Verification`.
Only completed continuation modules are imported here. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut declarations : Array Name := #[]
  for (decl, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? decl then
      let m := env.header.moduleNames[idx.toNat]!.toString
      if m == "DFLSphere433" || m.startsWith "DFLSphere433." || m == "continuation" || m.startsWith "continuation." then
        declarations := declarations.push decl
  for decl in declarations.qsort Name.quickLt do
    let dependencies ← collectAxioms decl
    let unexpected := dependencies.filter fun dep =>
      dep != ``propext && dep != ``Classical.choice && dep != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected kernel dependencies for {decl}: {unexpected}"
    logInfo m!"OWNDECL {decl} KERNEL {dependencies}"
  logInfo m!"OWNDECL_COUNT {declarations.size}"
