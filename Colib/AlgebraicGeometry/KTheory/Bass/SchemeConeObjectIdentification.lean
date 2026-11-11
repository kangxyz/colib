/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeIndexTransport
public import Colib.KTheory.Bass.ConeTrack

/-! # The literal object of the geometric cone functor -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace KTheory.Bass.SchemeIteratedSeedTransition

/-- This object identification changes only the presentation of the original cone. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeConeObjectIdentification.lean:20"
  "adaptation" "Original exact identification of the same scheme cone and seed data."]
theorem coneFunctor_obj_eq (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    GeometricConeInterchange.coneFunctor.obj F = ConeTrack.diagram squareFunctor F := rfl

end KTheory.Bass.SchemeIteratedSeedTransition
