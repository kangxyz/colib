/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryIteratedNullComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryTwistedFiberComparison
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeIteratedSeedNullComparison
public import Colib.Topology.Prespectrum.FiberLiftNaturality

/-! # Same-null auxiliary-supported iterated fiber comparison -/
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

/-- The same original auxiliary null gives the actual iterated fiber lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryCurrentFiber.lean:39"
  "adaptation" "Original same-null fiber lift comparison with three actual stable component maps."]
def iteratedLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift ((iteratedRestriction f T).app X) ((iteratedEnlargement f T).app X)
    ((iteratedNull f T).homotopy X)

/-- The actual three stable component maps preserve the original auxiliary fiber lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryCurrentFiber.lean:82"
  "adaptation" "Original same-null fiber lift comparison with three actual stable component maps."]
theorem iterated_twisted_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (iteratedLift f T X) ↔ IsStableEquivalence (twistedLift f T X) := by
  exact homotopyFiberLift_isStableEquivalence_iff
    ((iteratedEnlargement f T).app X) ((iteratedRestriction f T).app X)
    ((twistedEnlargement f T).app X) ((twistedRestriction f T).app X)
    ((iteratedNull f T).homotopy X) ((twistedNull f T).homotopy X)
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap (fiberAction f T)).app X)
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap (ambientAction T)).app X)
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap (openAction f T)).app X)
    (congrArg (fun η => η.app X) (SchemeIteratedSeedTelescope.input_square
      (fiberAction f T) (ambientAction T) _ (enlargement_equivariant f T)))
    (congrArg (fun η => η.app X) (SchemeIteratedSeedTelescope.input_square
      (ambientAction T) (openAction f T) _ (restriction_equivariant f T))).symm
    (fun n r x => iterated_null_square f T X n r x)
    (SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
      (fiber f T) (fiberAction f T) X)
    (SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
      (ambient T) (ambientAction T) X)
    (SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
      (openModel f T) (openAction f T) X)

/-- Current-stage and original iterated-seed auxiliary lifts have the same stability property. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryCurrentFiber.lean:104"
  "adaptation" "Original same-null fiber lift comparison with three actual stable component maps."]
theorem current_iterated_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (currentLift f T X) ↔ IsStableEquivalence (iteratedLift f T X) :=
  (current_normalized_lift_stable_iff f T X).trans
    ((normalized_twisted_lift_stable_iff f T X).trans
      (iterated_twisted_lift_stable_iff f T X).symm)

end AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber
