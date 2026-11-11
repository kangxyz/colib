/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliarySupportNull
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeInputNull

/-! # The actual auxiliary-support maps and original null
on the current and normalized telescopes -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
open SchemeNaturalSeed NaturalTrack
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The original forward Laurent action on union-supported objects. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:24"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
abbrev fiberAction := supportedTrack (unionOpen f T).ι

/-- The original forward Laurent action on the ambient auxiliary support. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:27"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
abbrev ambientAction := supportedTrack T.ι

/-- The original forward Laurent action on the inverse-image support. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:30"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
abbrev openAction := supportedTrack (inverseOpen f T).ι

/-- The actual enlargement after the original prespectrum realization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:33"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def firstMap := Functor.whiskerRight (enlargement f T) prespectrumFunctor

/-- The actual support restriction after the original prespectrum realization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:36"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def secondMap := Functor.whiskerRight (restriction f T) prespectrumFunctor

/-- Every original null slice preserves the same Laurent action. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:39"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem timeSlice_equivariant (r : unitInterval) :
    Equivariant (fiberAction f T) (openAction f T)
      (diagramHomotopyAt (η := firstMap f T ≫ secondMap f T)
        (θ := diagramZeroMap (fiber f T ⋙ prespectrumFunctor)
          (openModel f T ⋙ prespectrumFunctor))
        (fullNull f T).homotopy (fullNull f T).naturality r) := by
  intro X t
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  ext x
  exact (fullNull_laurentInterchange f T X n r t x).symm

/-- The actual auxiliary enlargement on the current telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:52"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def currentEnlargement := currentInputMap (fiberAction f T) (ambientAction T)
  (firstMap f T) (enlargement_equivariant f T)

/-- The actual auxiliary restriction on the current telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:56"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def currentRestriction := currentInputMap (ambientAction T) (openAction f T)
  (secondMap f T) (restriction_equivariant f T)

/-- Jointly continuous descent of the original auxiliary null to the current telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:60"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def currentNull := currentInputNull (fiberAction f T) (ambientAction T) (openAction f T)
  (firstMap f T) (secondMap f T) (enlargement_equivariant f T)
  (restriction_equivariant f T) (fullNull f T) (timeSlice_equivariant f T)

/-- The actual auxiliary enlargement on the normalized telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:65"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def normalizedEnlargement := normalizedInputMap (fiberAction f T) (ambientAction T)
  (firstMap f T) (enlargement_equivariant f T)

/-- The actual auxiliary restriction on the normalized telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:69"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def normalizedRestriction := normalizedInputMap (ambientAction T) (openAction f T)
  (secondMap f T) (restriction_equivariant f T)

/-- Jointly continuous descent of the original auxiliary null to the normalized telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:73"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def normalizedNull := normalizedInputNull (fiberAction f T) (ambientAction T) (openAction f T)
  (firstMap f T) (secondMap f T) (enlargement_equivariant f T)
  (restriction_equivariant f T) (fullNull f T) (timeSlice_equivariant f T)

/-- The original whole auxiliary null is preserved by the actual current/normalized comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:104"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem current_null_square (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((currentTelescope (fiberAction f T)).obj X).space n) :
    ((telescopeMap (openAction f T)).app X).map n
      (((currentNull f T).homotopy X).level n (r, x)) =
      ((normalizedNull f T).homotopy X).level n
        (r, ((telescopeMap (fiberAction f T)).app X).map n x) :=
  telescopeMap_null _ _ _ _ _ (enlargement_equivariant f T)
    (restriction_equivariant f T) (fullNull f T) (timeSlice_equivariant f T) X n r x


end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport

namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport

attribute [colib_tag "COL-0569"] current_null_square

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
