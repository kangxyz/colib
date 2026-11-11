/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullTwistedFiberComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterIteratedFullNull
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeIteratedSeedNullComparison
public import Colib.Topology.Prespectrum.FiberLiftNaturality

/-! # The actual original-to-twisted full-open fiber comparison -/
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

/-- Actual three-object stable comparison transports the original full-open fiber lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterIteratedTwistedFiber.lean:26"
  "adaptation" "Original same-null fiber lift comparison with three actual stable component maps."]
theorem iterated_twisted_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (iteratedLift f X) ↔ IsStableEquivalence (twistedLift f X) := by
  exact homotopyFiberLift_isStableEquivalence_iff
    ((iteratedForget f).app X) ((iteratedOpen f).app X)
    ((twistedForget f).app X) ((twistedOpen f).app X)
    ((iteratedNull f).homotopy X) ((twistedNull f).homotopy X)
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap (supportedTrack f)).app X)
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap (ambientTrack Q)).app X)
      ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap (ambientTrack P)).app X)
    (congrArg (fun η => η.app X) (SchemeIteratedSeedTelescope.input_square
      (supportedTrack f) (ambientTrack Q) _ (forget_equivariant f)))
    (congrArg (fun η => η.app X) (SchemeIteratedSeedTelescope.input_square
      (ambientTrack Q) (ambientTrack P) _ (fullMap_equivariant f))).symm
    (fun n r x => SchemeIteratedSeedTelescope.null_square
      (supportedTrack f) (ambientTrack Q) (ambientTrack P) _ _
      (forget_equivariant f) (fullMap_equivariant f)
      (fullNull f) (timeSlice_equivariant f) X n r x)
    (SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
      (ParameterModels.supported f) (supportedTrack f) X)
    (SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
      (ParameterModels.ambient Q) (ambientTrack Q) X)
    (SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
      (ParameterModels.ambient P) (ambientTrack P) X)

end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull

namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull

attribute [colib_tag "COL-0585"] iterated_twisted_lift_stable_iff

end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
