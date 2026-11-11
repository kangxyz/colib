/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorPresentation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullCurrentNull

/-! # Original full-open map and whole-null normalized tensor actions

Auxiliary actions are deferred to their actual geometric support predecessors. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
open GlobalSectionChangeIndex GlobalSupportedSection NaturalTrack ParameterTensorNormalizedTrack
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The original full-open map preserves the actual normalized tensor track. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterTensorPresentationActions.lean:30"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem fullMap_equivariant : Equivariant (ambientTrack Q) (ambientTrack P)
    (ParameterFullCurrentNull.fullMap f) := by
  rw [ambientTrack_eq, ambientTrack_eq]
  exact ParameterFullCurrentNull.fullMap_equivariant f

/-- Every original basic null slice keeps its time and its normalized tensor action. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterTensorPresentationActions.lean:36"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem fullNull_equivariant (r : unitInterval) :
    Equivariant (supportedTrack f) (ambientTrack P)
      (diagramHomotopyAt
        (η := Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor ≫
          ParameterFullCurrentNull.fullMap f)
        (θ := diagramZeroMap (ParameterModels.supported f ⋙ prespectrumFunctor)
          (ParameterModels.ambient P ⋙ prespectrumFunctor))
        (ParameterFullCurrentNull.fullNull f).homotopy
        (ParameterFullCurrentNull.fullNull f).naturality r) := by
  rw [supportedTrack_eq, ambientTrack_eq]
  exact ParameterFullCurrentNull.timeSlice_equivariant f r


end AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
