/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeConeObjectIdentification

/-! # Literal prespectrum values of the original geometric cone -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u v w
namespace KTheory.Bass.SchemeIteratedSeedTransition

/-- Evaluation of the fixed cone diagram is the original mapping cone. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeConeValueIdentification.lean:19"
  "adaptation" "Original exact identification of the same scheme cone and seed data."]
theorem coneDiagram_obj_eq {C : Type u} [Category.{v} C]
    (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w}) (X : C) :
    (ConeTrack.diagram Q F).obj X =
      mappingCone (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))) := rfl

/-- The geometric cone value uses precisely the same original square comparison. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeConeValueIdentification.lean:25"
  "adaptation" "Original exact identification of the same scheme cone and seed data."]
theorem coneFunctor_obj_obj_eq (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) :
    (GeometricConeInterchange.coneFunctor.obj F).obj X =
      mappingCone (StrictSquare.comparison (F.mapArrow.mapArrow.obj (square X))) := rfl

end KTheory.Bass.SchemeIteratedSeedTransition
