/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullCurrentNull
public import Colib.Topology.Prespectrum.FiberLiftNaturality
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentStageTelescopeStable

/-! # Same-null full-open fiber-lift stability across the actual current and normalized diagrams -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
open SchemeNaturalSeed
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The actual current supported inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullFiberComparison.lean:24"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def currentForget := currentInputMap (supportedTrack f) (ambientTrack Q)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (forget_equivariant f)

/-- The actual current full-open map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullFiberComparison.lean:28"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def currentOpen := currentInputMap (ambientTrack Q) (ambientTrack P)
  (fullMap f) (fullMap_equivariant f)

/-- The original same-null full-open lift on the current model. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullFiberComparison.lean:32"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def currentLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift ((currentOpen f).app X) ((currentForget f).app X)
    ((currentNull f).homotopy X)

/-- The actual normalized supported inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullFiberComparison.lean:37"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def normalizedForget := normalizedInputMap (supportedTrack f) (ambientTrack Q)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (forget_equivariant f)

/-- The actual normalized full-open map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullFiberComparison.lean:41"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def normalizedOpen := normalizedInputMap (ambientTrack Q) (ambientTrack P)
  (fullMap f) (fullMap_equivariant f)

/-- The original same-null full-open lift on the normalized model. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullFiberComparison.lean:45"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def normalizedLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift ((normalizedOpen f).app X) ((normalizedForget f).app X)
    ((normalizedNull f).homotopy X)

/-- Actual three-object stable comparison transports the original full-open fiber lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullFiberComparison.lean:63"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem current_normalized_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (currentLift f X) ↔ IsStableEquivalence (normalizedLift f X) := by
  exact homotopyFiberLift_isStableEquivalence_iff
    ((currentForget f).app X) ((currentOpen f).app X)
    ((normalizedForget f).app X) ((normalizedOpen f).app X)
    ((currentNull f).homotopy X) ((normalizedNull f).homotopy X)
    ((telescopeMap (supportedTrack f)).app X)
    ((telescopeMap (ambientTrack Q)).app X) ((telescopeMap (ambientTrack P)).app X)
    (congrArg (fun η => η.app X) (telescopeMap_input_square
      (supportedTrack f) (ambientTrack Q) _ (forget_equivariant f)))
    (congrArg (fun η => η.app X) (telescopeMap_input_square
      (ambientTrack Q) (ambientTrack P) _ (fullMap_equivariant f))).symm
    (fun n r x => current_null_square f X n r x)
    (model_telescopeMap_stable (ParameterModels.supported f) (supportedTrack f) X)
    (model_telescopeMap_stable (ParameterModels.ambient Q) (ambientTrack Q) X)
    (model_telescopeMap_stable (ParameterModels.ambient P) (ambientTrack P) X)


end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull

namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull

attribute [colib_tag "COL-0570"] current_normalized_lift_stable_iff

end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
