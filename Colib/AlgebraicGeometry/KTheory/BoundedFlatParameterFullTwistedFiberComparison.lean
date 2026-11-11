/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullCurrentFiberComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullTwistedNull
public import Colib.Topology.Prespectrum.FiberLiftNaturality
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedTelescope

/-! # Same-null normalized and twisted fiber-lift comparison -/
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

/-- The actual twisted supported inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullFiberComparison.lean:50"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def twistedForget := twistedInputMap (supportedTrack f) (ambientTrack Q)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (forget_equivariant f)

/-- The actual twisted full-open map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullFiberComparison.lean:54"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def twistedOpen := twistedInputMap (ambientTrack Q) (ambientTrack P)
  (fullMap f) (fullMap_equivariant f)

/-- The original same-null full-open lift on the twisted model. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullFiberComparison.lean:58"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def twistedLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift ((twistedOpen f).app X) ((twistedForget f).app X)
    ((twistedNull f).homotopy X)

/-- Actual three-object stable comparison transports the original full-open fiber lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullFiberComparison.lean:81"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem normalized_twisted_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (normalizedLift f X) ↔ IsStableEquivalence (twistedLift f X) := by
  exact homotopyFiberLift_isStableEquivalence_iff
    ((normalizedForget f).app X) ((normalizedOpen f).app X)
    ((twistedForget f).app X) ((twistedOpen f).app X)
    ((normalizedNull f).homotopy X) ((twistedNull f).homotopy X)
    ((conjugacyTelescopeMap (supportedTrack f)).app X)
    ((conjugacyTelescopeMap (ambientTrack Q)).app X) ((conjugacyTelescopeMap (ambientTrack
      P)).app X)
    (congrArg (fun η => η.app X) (conjugacyTelescopeMap_input_square
      (supportedTrack f) (ambientTrack Q) _ (forget_equivariant f)))
    (congrArg (fun η => η.app X) (conjugacyTelescopeMap_input_square
      (ambientTrack Q) (ambientTrack P) _ (fullMap_equivariant f))).symm
    (fun n r x => twisted_null_square f X n r x)
    (model_conjugacyTelescopeMap_stable (ParameterModels.supported f) (supportedTrack f) X)
    (model_conjugacyTelescopeMap_stable (ParameterModels.ambient Q) (ambientTrack Q) X)
    (model_conjugacyTelescopeMap_stable (ParameterModels.ambient P) (ambientTrack P) X)

/-- The two original comparisons give the same-null current/twisted stability equivalence. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterFullFiberComparison.lean:100"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem current_twisted_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (currentLift f X) ↔ IsStableEquivalence (twistedLift f X) :=
  (current_normalized_lift_stable_iff f X).trans (normalized_twisted_lift_stable_iff f X)

end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull

namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull

attribute [colib_tag "COL-0575"] normalized_twisted_lift_stable_iff

end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull

namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull

attribute [colib_tag "COL-0575"] current_twisted_lift_stable_iff

end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
