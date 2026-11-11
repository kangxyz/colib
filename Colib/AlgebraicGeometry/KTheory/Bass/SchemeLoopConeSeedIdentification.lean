/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeLoopConeTrackIdentification
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeBassFunctorIdentification

/-! # The unchanged looped cone seed in the geometric cospan -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace KTheory.Bass.SchemeIteratedSeedTransition
open NaturalTrack GeometricSeedCospan SchemeNaturalSeed
open FiniteConeTopology
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The looped cone seed is the original geometric cospan seed, including its endpoint casts. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeLoopConeSeedIdentification.lean:26"
  "adaptation" "Original exact identification of the same scheme cone and seed data."]
theorem seed_loopCone_heq_bassSeed (A : Track laurent.op coefficient F) :
    HEq (seed ((coneTrack A 1).loop))
      (WholeSeedCospan.seed
        (GeometricSquareInterchange.geometricSquare
          ((strictDiagramFunctor squareFunctor).obj F))
        (bassTrack F A.homotopy A.naturality)
        (bassTrack_naturality F A.homotopy A.naturality)) := by
  simp only [seed, sourceTrack_loopConeTrack A]
  dsimp only [bassFunctor_obj_eq, iterate]
  rfl

end KTheory.Bass.SchemeIteratedSeedTransition
