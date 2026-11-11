/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryCurrentFiber
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryTwistedNull
public import Colib.Topology.Prespectrum.FiberLiftNaturality
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedTelescope

/-! # Same-null normalized and twisted fiber-lift comparison -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
open SchemeNaturalSeed
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The same original auxiliary null gives the actual twisted fiber lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryCurrentFiber.lean:34"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def twistedLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift ((twistedRestriction f T).app X) ((twistedEnlargement f T).app X)
    ((twistedNull f T).homotopy X)

/-- The actual three stable component maps preserve the original auxiliary fiber lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryCurrentFiber.lean:63"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem normalized_twisted_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (normalizedLift f T X) ↔ IsStableEquivalence (twistedLift f T X) := by
  exact homotopyFiberLift_isStableEquivalence_iff
    ((normalizedEnlargement f T).app X) ((normalizedRestriction f T).app X)
    ((twistedEnlargement f T).app X) ((twistedRestriction f T).app X)
    ((normalizedNull f T).homotopy X) ((twistedNull f T).homotopy X)
    ((conjugacyTelescopeMap (fiberAction f T)).app X)
    ((conjugacyTelescopeMap (ambientAction T)).app X)
    ((conjugacyTelescopeMap (openAction f T)).app X)
    (congrArg (fun η => η.app X) (conjugacyTelescopeMap_input_square
      (fiberAction f T) (ambientAction T) _ (enlargement_equivariant f T)))
    (congrArg (fun η => η.app X) (conjugacyTelescopeMap_input_square
      (ambientAction T) (openAction f T) _ (restriction_equivariant f T))).symm
    (fun n r x => twisted_null_square f T X n r x)
    (model_conjugacyTelescopeMap_stable (fiber f T) (fiberAction f T) X)
    (model_conjugacyTelescopeMap_stable (ambient T) (ambientAction T) X)
    (model_conjugacyTelescopeMap_stable (openModel f T) (openAction f T) X)


end AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber

namespace AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber

attribute [colib_tag "COL-0575"] normalized_twisted_lift_stable_iff

end AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber
