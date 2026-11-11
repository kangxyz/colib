/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeIndexTransport
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare
universe u w
namespace KTheory.Bass.GeometricConeInterchange

variable {T T' : Scheme.{u}} (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q' : T' ⟶ (Spec (.of (ULift.{u} ℤ))))
    (f : T ⟶ T') (hf : f ≫ q' = q) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})

example : (baseProductFunctor q).op ⋙ coneFunctor.obj F ≅
    coneFunctor.obj ((baseProductFunctor q).op ⋙ F) :=
  eta q F

example (X : Scheme.{u}ᵒᵖ) :
    (eta q F).hom.app X = totalFunctor.map (F.mapArrow.mapArrow.map (squareIso q X).hom) :=
  eta_hom_app q F X

example :
    Functor.whiskerRight (NatTrans.op (baseProductTransformation q q' f hf))
        (coneFunctor.obj F) ≫ (eta q F).hom =
      (eta q' F).hom ≫ coneFunctor.map
        (Functor.whiskerRight (NatTrans.op (baseProductTransformation q q' f hf)) F) :=
  eta_factor q q' f hf F

example :
    Functor.whiskerRight (NatTrans.op (baseProductProjection q))
        (coneFunctor.obj F) ≫ (eta q F).hom =
      coneFunctor.map (Functor.whiskerRight (NatTrans.op (baseProductProjection q)) F) :=
  eta_projection q F

example (X : Scheme.{u}ᵒᵖ) : Arrow (Arrow (Arrow (Arrow LoopPrespectrum.{w}))) :=
  diagram F X

example (X : Scheme.{u}ᵒᵖ) : Arrow (Arrow LoopPrespectrum.{w}) :=
  target F X

end KTheory.Bass.GeometricConeInterchange
end
