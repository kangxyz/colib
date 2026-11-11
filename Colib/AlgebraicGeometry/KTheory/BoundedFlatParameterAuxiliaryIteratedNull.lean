/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryTwistedNull
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeIteratedInputNull

/-! # The actual auxiliary-support maps and original null on the iterated telescope -/
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

/-- The actual auxiliary enlargement on the iterated telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:91"
  "adaptation" "Original selected full and auxiliary null on the actual seed-iterate telescope."]
def iteratedEnlargement := iteratedInputMap (fiberAction f T) (ambientAction T)
  (firstMap f T) (enlargement_equivariant f T)

/-- The actual auxiliary restriction on the iterated telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:95"
  "adaptation" "Original selected full and auxiliary null on the actual seed-iterate telescope."]
def iteratedRestriction := iteratedInputMap (ambientAction T) (openAction f T)
  (secondMap f T) (restriction_equivariant f T)

/-- Jointly continuous descent of the original auxiliary null to the iterated telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryTelescopeNull.lean:99"
  "adaptation" "Original selected full and auxiliary null on the actual seed-iterate telescope."]
def iteratedNull := iteratedInputNull (fiberAction f T) (ambientAction T) (openAction f T)
  (firstMap f T) (secondMap f T) (enlargement_equivariant f T)
  (restriction_equivariant f T) (fullNull f T) (timeSlice_equivariant f T)

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
