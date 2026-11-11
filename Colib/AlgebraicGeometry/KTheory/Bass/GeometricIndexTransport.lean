/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricIndexSquare
public import Colib.KTheory.Bass.DiagramSquareNull

/-!
# Actual geometric Bass factor transports

The four original integer-base swaps give a natural square isomorphism between
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
variable {T T' : Scheme.{u}} (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
  (q' : T' ⟶ (Spec (.of (ULift.{u} ℤ))))
  (f : T ⟶ T') (hf : f ≫ q' = q) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})

/-- The original four-corner cone/loop image of index interchange. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricIndexTransport.lean:34"
  "adaptation" "Original actual factor swap and full diagram transport."]
def eta : (baseProductFunctor q).op ⋙ (strictDiagramFunctor squareFunctor).obj F ≅
    (strictDiagramFunctor squareFunctor).obj ((baseProductFunctor q).op ⋙ F) :=
  Functor.isoWhiskerRight (interchange q) (F.mapArrow.mapArrow ⋙ strictSquareLoopedConeFunctor)


/-- Its components retain the actual four original swaps. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricIndexTransport.lean:39"
  "adaptation" "Original actual factor swap and full diagram transport."]
theorem eta_hom_app (X : Scheme.{u}ᵒᵖ) :
    (eta q F).hom.app X = strictSquareLoopedConeFunctor.map
      (F.mapArrow.mapArrow.map (squareIso q X).hom) := rfl


/-- Naturality in the independent factor retains the actual factor map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricIndexTransport.lean:44"
  "adaptation" "Original actual factor swap and full diagram transport."]
theorem eta_factor :
    Functor.whiskerRight (NatTrans.op (baseProductTransformation q q' f hf))
        ((strictDiagramFunctor squareFunctor).obj F) ≫ (eta q F).hom =
      (eta q' F).hom ≫ (strictDiagramFunctor squareFunctor).map
        (Functor.whiskerRight (NatTrans.op (baseProductTransformation q q' f hf)) F) := by
  apply NatTrans.ext
  funext X
  let K := F.mapArrow.mapArrow ⋙ strictSquareLoopedConeFunctor
  change K.map (squareFunctor.map ((baseProductTransformation q q' f hf).app X.unop).op) ≫
      K.map (squareIso q X).hom = K.map (squareIso q' X).hom ≫
        K.map (onSquare (NatTrans.op (baseProductTransformation q q' f hf)) (square X))
  rw [← K.map_comp, ← K.map_comp, squareIso_factor]


/-- The source projection is preserved by the original factor interchange. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricIndexTransport.lean:58"
  "adaptation" "Original actual factor swap and full diagram transport."]
theorem eta_projection :
    Functor.whiskerRight (NatTrans.op (baseProductProjection q))
        ((strictDiagramFunctor squareFunctor).obj F) ≫ (eta q F).hom =
      (strictDiagramFunctor squareFunctor).map
        (Functor.whiskerRight (NatTrans.op (baseProductProjection q)) F) := by
  apply NatTrans.ext
  funext X
  let K := F.mapArrow.mapArrow ⋙ strictSquareLoopedConeFunctor
  change K.map (squareFunctor.map ((baseProductProjection q).app X.unop).op) ≫
      K.map (squareIso q X).hom =
        K.map (onSquare (NatTrans.op (baseProductProjection q)) (square X))
  rw [← K.map_comp, squareIso_projection]


/-- Every component is the original geometric square, with all four original maps. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricIndexTransport.lean:100"
  "adaptation" "Original actual factor swap and full diagram transport."]
theorem geometricSquare_component (X : Scheme.{u}ᵒᵖ) :
    (SquareConeStrength.squareDiagram (geometricSquare F)).obj X =
      F.mapArrow.mapArrow.obj (square X) := rfl


/-- The polynomial source equation in the literal source functors used by the square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricIndexTransport.lean:105"
  "adaptation" "Original actual factor swap and full diagram transport."]
theorem projectionMap_eta :
    projectionMap ((strictDiagramFunctor squareFunctor).obj F) ≫
        (eta (polynomialProjection (.of (ULift.{u} ℤ))) F).hom =
      (strictDiagramFunctor squareFunctor).map (projectionMap F) := by
  apply NatTrans.ext
  funext X
  exact congrArg (fun k => k.app X)
    (eta_projection (polynomialProjection (.of (ULift.{u} ℤ))) F)


/-- Remove only the literal identity from a specified compositional equation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricIndexTransport.lean:115"
  "adaptation" "Original actual factor swap and full diagram transport."]
theorem id_comp_of_comp_eq {D : Type u₁} [Category.{v₁} D]
    {X Y Z : D} {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z} (h : f ≫ g = k) :
    𝟙 X ≫ k = f ≫ g := (Category.id_comp k).trans h.symm


end KTheory.Bass.GeometricSquareInterchange
