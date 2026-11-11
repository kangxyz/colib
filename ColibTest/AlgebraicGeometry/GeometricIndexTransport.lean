/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricIndexTransport
noncomputable section
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

example : (baseProductFunctor q).op ⋙ (strictDiagramFunctor squareFunctor).obj F ≅
    (strictDiagramFunctor squareFunctor).obj ((baseProductFunctor q).op ⋙ F) :=
  eta q F

example (X : Scheme.{u}ᵒᵖ) :
    (eta q F).hom.app X = strictSquareLoopedConeFunctor.map
      (F.mapArrow.mapArrow.map (squareIso q X).hom) :=
  eta_hom_app q F X

example :
    Functor.whiskerRight (NatTrans.op (baseProductTransformation q q' f hf))
        ((strictDiagramFunctor squareFunctor).obj F) ≫ (eta q F).hom =
      (eta q' F).hom ≫ (strictDiagramFunctor squareFunctor).map
        (Functor.whiskerRight (NatTrans.op (baseProductTransformation q q' f hf)) F) :=
  eta_factor q q' f hf F

example :
    Functor.whiskerRight (NatTrans.op (baseProductProjection q))
        ((strictDiagramFunctor squareFunctor).obj F) ≫ (eta q F).hom =
      (strictDiagramFunctor squareFunctor).map
        (Functor.whiskerRight (NatTrans.op (baseProductProjection q)) F) :=
  eta_projection q F

example (X : Scheme.{u}ᵒᵖ) :
    (SquareConeStrength.squareDiagram (geometricSquare F)).obj X =
      F.mapArrow.mapArrow.obj (square X) :=
  geometricSquare_component F X

example :
    projectionMap ((strictDiagramFunctor squareFunctor).obj F) ≫
        (eta (polynomialProjection (.of (ULift.{u} ℤ))) F).hom =
      (strictDiagramFunctor squareFunctor).map (projectionMap F) :=
  projectionMap_eta F

end KTheory.Bass.GeometricSquareInterchange
end
