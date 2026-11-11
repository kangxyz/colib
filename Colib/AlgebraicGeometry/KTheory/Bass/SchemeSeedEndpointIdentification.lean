/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeConeValueIdentification
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricSeedCospan
public import Colib.KTheory.Bass.LoopFactor

/-! # The source and parameter-loop endpoints of the original seed -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace KTheory.Bass.SchemeIteratedSeedTransition

/-- The original geometric square starts at the unchanged input diagram. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeSeedEndpointIdentification.lean:21"
  "adaptation" "Original exact identification of the same scheme cone and seed data."]
theorem geometricSquare_source_eq (G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    (GeometricSquareInterchange.geometricSquare G).left.left = G := rfl

/-- A looped diagram has the literal parameter-loop value. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeSeedEndpointIdentification.lean:25"
  "adaptation" "Original exact identification of the same scheme cone and seed data."]
theorem loop_comp_obj_eq (G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    (G ⋙ parameterLoopingFunctor).obj X = parameterLooping (G.obj X) := rfl

/-- Evaluation of a looped diagram gives the original loop square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeSeedEndpointIdentification.lean:29"
  "adaptation" "Original exact identification of the same scheme cone and seed data."]
theorem loop_comp_square_eq (G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    (G ⋙ parameterLoopingFunctor).mapArrow.mapArrow.obj (square X) =
      LoopFactor.loopSquare (G.mapArrow.mapArrow.obj (square X)) := rfl

end KTheory.Bass.SchemeIteratedSeedTransition
