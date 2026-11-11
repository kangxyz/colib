/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryCurrentNull
public import Colib.Topology.Prespectrum.FiberLiftNaturality
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentStageTelescopeStable

/-! # Same-null auxiliary-supported fiber comparison
across the actual current and normalized diagrams -/
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

/-- The same original auxiliary null gives the actual current fiber lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryCurrentFiber.lean:24"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def currentLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift ((currentRestriction f T).app X) ((currentEnlargement f T).app X)
    ((currentNull f T).homotopy X)

/-- The same original auxiliary null gives the actual normalized fiber lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryCurrentFiber.lean:29"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def normalizedLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift ((normalizedRestriction f T).app X) ((normalizedEnlargement f T).app X)
    ((normalizedNull f T).homotopy X)

/-- The actual three stable component maps preserve the original auxiliary fiber lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryCurrentFiber.lean:44"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem current_normalized_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (currentLift f T X) ↔ IsStableEquivalence (normalizedLift f T X) := by
  exact homotopyFiberLift_isStableEquivalence_iff
    ((currentEnlargement f T).app X) ((currentRestriction f T).app X)
    ((normalizedEnlargement f T).app X) ((normalizedRestriction f T).app X)
    ((currentNull f T).homotopy X) ((normalizedNull f T).homotopy X)
    ((telescopeMap (fiberAction f T)).app X)
    ((telescopeMap (ambientAction T)).app X)
    ((telescopeMap (openAction f T)).app X)
    (congrArg (fun η => η.app X) (telescopeMap_input_square
      (fiberAction f T) (ambientAction T) _ (enlargement_equivariant f T)))
    (congrArg (fun η => η.app X) (telescopeMap_input_square
      (ambientAction T) (openAction f T) _ (restriction_equivariant f T))).symm
    (fun n r x => current_null_square f T X n r x)
    (model_telescopeMap_stable (fiber f T) (fiberAction f T) X)
    (model_telescopeMap_stable (ambient T) (ambientAction T) X)
    (model_telescopeMap_stable (openModel f T) (openAction f T) X)


end AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber

namespace AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber

attribute [colib_tag "COL-0570"] current_normalized_lift_stable_iff

end AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber
