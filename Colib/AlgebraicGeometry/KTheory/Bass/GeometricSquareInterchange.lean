/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricIndexTransport
public import Colib.CategoryTheory.ArrowSquareMap

/-!
# The actual geometric Bass square interchange

The four original integer-base swaps give a natural square map between
applying the geometric square after Bass and applying Bass to the original
square. Its edges use the proved factor projection and positive/inverse charts.
No unit-track or seed compatibility is assumed here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
universe u w u₁ v₁
namespace KTheory.Bass.GeometricSquareInterchange
variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})

/-- The actual four eta maps form the geometric square map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricSquareInterchange.lean:33"
  "adaptation" "Original four-corner map to the literal functor image of a square."]
def squareInterchangeMap : geometricSquare ((strictDiagramFunctor squareFunctor).obj F) ⟶
    (strictDiagramFunctor squareFunctor).mapArrow.mapArrow.obj (geometricSquare F) :=
  Arrow.squareMapHomMk (strictDiagramFunctor squareFunctor) (geometricSquare F)
    (geometricSquare ((strictDiagramFunctor squareFunctor).obj F))
    (𝟙 ((strictDiagramFunctor squareFunctor).obj F))
    (eta (polynomialProjection (.of (ULift.{u} ℤ))) F).hom
    (eta (polynomialProjection (.of (ULift.{u} ℤ))) F).hom
    (eta (laurentProjection (.of (ULift.{u} ℤ))) F).hom
    (id_comp_of_comp_eq (projectionMap_eta F))
    (id_comp_of_comp_eq (projectionMap_eta F))
    (eta_factor (laurentProjection (.of (ULift.{u} ℤ)))
      (polynomialProjection (.of (ULift.{u} ℤ))) (laurentToPolynomial (.of (ULift.{u} ℤ)))
      (laurentToPolynomial_projection (.of (ULift.{u} ℤ))) F).symm
    (eta_factor (laurentProjection (.of (ULift.{u} ℤ)))
      (polynomialProjection (.of (ULift.{u} ℤ))) (laurentMinus (.of (ULift.{u} ℤ)))
      (laurentMinus_projection (.of (ULift.{u} ℤ))) F).symm

/-- The source corner is exactly identity, without a replacement equivalence. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricSquareInterchange.lean:51"
  "adaptation" "Original four-corner map to the literal functor image of a square."]
theorem squareInterchange_base : (squareInterchangeMap F).left.left =
    𝟙 ((strictDiagramFunctor squareFunctor).obj F) := by
  apply NatTrans.ext
  funext X
  rfl

/-- Both polynomial corners are the original eta at the actual polynomial factor. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricSquareInterchange.lean:58"
  "adaptation" "Original four-corner map to the literal functor image of a square."]
theorem squareInterchange_polynomial : (squareInterchangeMap F).left.right =
    (eta (polynomialProjection (.of (ULift.{u} ℤ))) F).hom :=
  Arrow.squareMapHomMk_left_right _ _ _ _ _ _ _ _ _ _ _

/-- The Laurent corner is the original eta at the actual Laurent factor. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricSquareInterchange.lean:63"
  "adaptation" "Original four-corner map to the literal functor image of a square."]
theorem squareInterchange_laurent : (squareInterchangeMap F).right.right =
    (eta (laurentProjection (.of (ULift.{u} ℤ))) F).hom :=
  Arrow.squareMapHomMk_right_right _ _ _ _ _ _ _ _ _ _ _

end KTheory.Bass.GeometricSquareInterchange
