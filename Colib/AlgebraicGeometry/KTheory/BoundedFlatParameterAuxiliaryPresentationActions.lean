/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryCurrentNull

/-! Original basic and auxiliary arrows and null slices preserve
the genuine normalized tensor tracks. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
open GlobalSectionChangeIndex GlobalSupportedSection NaturalTrack ParameterTensorNormalizedTrack
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

open ParameterAuxiliarySupport
variable (T : Q.Opens)

/-- The actual union-support enlargement preserves the same normalized tensor action. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterTensorPresentationActions.lean:52"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem enlargement_equivariant :
    Equivariant (supportedTrack (unionOpen f T).ι) (supportedTrack T.ι) (firstMap f T) := by
  rw [supportedTrack_eq, supportedTrack_eq]
  exact ParameterAuxiliarySupport.enlargement_equivariant f T

omit [IsOpenImmersion f] in
/-- The actual inverse-image support restriction preserves that normalized tensor action. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterTensorPresentationActions.lean:59"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem restriction_equivariant :
    Equivariant (supportedTrack T.ι) (supportedTrack (inverseOpen f T).ι) (secondMap f T) := by
  rw [supportedTrack_eq, supportedTrack_eq]
  exact ParameterAuxiliarySupport.restriction_equivariant f T

/-- Every original auxiliary null slice retains its actual two-time tensor interchange. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterTensorPresentationActions.lean:65"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem auxiliaryNull_equivariant (r : unitInterval) :
    Equivariant (supportedTrack (unionOpen f T).ι) (supportedTrack (inverseOpen f T).ι)
      (diagramHomotopyAt (η := firstMap f T ≫ secondMap f T)
        (θ := diagramZeroMap (fiber f T ⋙ prespectrumFunctor)
          (openModel f T ⋙ prespectrumFunctor))
        (fullNull f T).homotopy (fullNull f T).naturality r) := by
  rw [supportedTrack_eq, supportedTrack_eq]
  exact ParameterAuxiliarySupport.timeSlice_equivariant f T r

end AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
