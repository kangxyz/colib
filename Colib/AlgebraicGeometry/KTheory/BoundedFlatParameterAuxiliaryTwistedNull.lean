/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryCurrentNull
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedNull

/-! # Original same-null comparison with the actual twisted telescope -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
open KTheory.Bass.SchemeNaturalSeed KTheory.Bass.NaturalTrack
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The actual auxiliary enlargement on the twisted telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:78"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def twistedEnlargement := twistedInputMap (fiberAction f T) (ambientAction T)
  (firstMap f T) (enlargement_equivariant f T)


/-- The actual auxiliary restriction on the twisted telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:82"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def twistedRestriction := twistedInputMap (ambientAction T) (openAction f T)
  (secondMap f T) (restriction_equivariant f T)


/-- Jointly continuous descent of the original auxiliary null to the twisted telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:86"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def twistedNull := twistedInputNull (fiberAction f T) (ambientAction T) (openAction f T)
  (firstMap f T) (secondMap f T) (enlargement_equivariant f T)
  (restriction_equivariant f T) (fullNull f T) (timeSlice_equivariant f T)


/-- The original whole auxiliary null is preserved by the actual normalized/twisted comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:114"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem twisted_null_square (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((normalizedTelescope (fiberAction f T)).obj X).space n) :
    ((conjugacyTelescopeMap (openAction f T)).app X).map n
      (((normalizedNull f T).homotopy X).level n (r, x)) =
      ((twistedNull f T).homotopy X).level n
        (r, ((conjugacyTelescopeMap (fiberAction f T)).app X).map n x) :=
  conjugacyTelescopeMap_null _ _ _ _ _ (enlargement_equivariant f T)
    (restriction_equivariant f T) (fullNull f T) (timeSlice_equivariant f T) X n r x


end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
