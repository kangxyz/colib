/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeSeedCospanIdentification

/-! # The original looped cone track with the geometric endpoint casts -/
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

/-- Looping the first actual cone action gives exactly the geometric cospan's track. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeLoopConeTrackIdentification.lean:25"
  "adaptation" "Original exact identification of the same scheme cone and seed data."]
theorem sourceTrack_loopConeTrack (A : Track laurent.op coefficient F) :
    sourceTrack (iterate squareFunctor 1 F ⋙ parameterLoopingFunctor)
      (coneTrack A 1).loop.homotopy = bassTrack F A.homotopy A.naturality := rfl

end KTheory.Bass.SchemeIteratedSeedTransition
