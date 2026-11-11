/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricIndexTransport
public import Colib.Topology.Prespectrum.StrictDoubleSquareCone

/-!
# The actual geometric target of double-cone interchange

The generic double totalization has the literal pointwise-cone target. The
original four factor interchanges identify that target with the original Bass
square of the unlooped cone. The two polynomial and Laurent components retain
their specified inverse swaps. No target renaming or seed coherence is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare
universe u w
namespace KTheory.Bass.GeometricConeInterchange

/-- The original unlooped Bass cone, acting on the actual strict diagram category. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeIndexTransport.lean:32"
  "adaptation" "Original independent-factor cone interchange and literal target square."]
def coneFunctor : (Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) ⥤
    (Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :=
  Functor.mapArrowFunctor _ LoopPrespectrum ⋙
    Functor.mapArrowFunctor _ (Arrow LoopPrespectrum) ⋙
    (Functor.whiskeringLeft _ _ (Arrow (Arrow LoopPrespectrum))).obj squareFunctor ⋙
    (Functor.whiskeringRight _ (Arrow (Arrow LoopPrespectrum)) LoopPrespectrum).obj totalFunctor

variable {T T' : Scheme.{u}} (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q' : T' ⟶ (Spec (.of (ULift.{u} ℤ))))
    (f : T ⟶ T') (hf : f ≫ q' = q) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})

/-- The original unlooped cone image of the actual independent-factor index swap. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeIndexTransport.lean:43"
  "adaptation" "Original independent-factor cone interchange and literal target square."]
def eta : (baseProductFunctor q).op ⋙ coneFunctor.obj F ≅
    coneFunctor.obj ((baseProductFunctor q).op ⋙ F) :=
  Functor.isoWhiskerRight (interchange q) (F.mapArrow.mapArrow ⋙ totalFunctor)

/-- Its actual component is the original strict-square map on the original cone. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeIndexTransport.lean:48"
  "adaptation" "Original independent-factor cone interchange and literal target square."]
theorem eta_hom_app (X : Scheme.{u}ᵒᵖ) :
    (eta q F).hom.app X = totalFunctor.map (F.mapArrow.mapArrow.map (squareIso q X).hom) := rfl

/-- The independent-factor map commutes with the full original cone interchange. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeIndexTransport.lean:52"
  "adaptation" "Original independent-factor cone interchange and literal target square."]
theorem eta_factor :
    Functor.whiskerRight (NatTrans.op (baseProductTransformation q q' f hf))
        (coneFunctor.obj F) ≫ (eta q F).hom =
      (eta q' F).hom ≫ coneFunctor.map
        (Functor.whiskerRight (NatTrans.op (baseProductTransformation q q' f hf)) F) := by
  apply NatTrans.ext
  funext X
  let K := F.mapArrow.mapArrow ⋙ totalFunctor
  change K.map (squareFunctor.map ((baseProductTransformation q q' f hf).app X.unop).op) ≫
      K.map (squareIso q X).hom = K.map (squareIso q' X).hom ≫
        K.map (onSquare (NatTrans.op (baseProductTransformation q q' f hf)) (square X))
  rw [← K.map_comp, ← K.map_comp, squareIso_factor]

/-- The original projection is preserved by the actual independent-factor map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeIndexTransport.lean:66"
  "adaptation" "Original independent-factor cone interchange and literal target square."]
theorem eta_projection :
    Functor.whiskerRight (NatTrans.op (baseProductProjection q))
        (coneFunctor.obj F) ≫ (eta q F).hom =
      coneFunctor.map (Functor.whiskerRight (NatTrans.op (baseProductProjection q)) F) := by
  apply NatTrans.ext
  funext X
  let K := F.mapArrow.mapArrow ⋙ totalFunctor
  change K.map (squareFunctor.map ((baseProductProjection q).app X.unop).op) ≫
      K.map (squareIso q X).hom =
        K.map (onSquare (NatTrans.op (baseProductProjection q)) (square X))
  rw [← K.map_comp, squareIso_projection]

/-- The original four-dimensional evaluation diagram, before either total quotient. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeIndexTransport.lean:79"
  "adaptation" "Original independent-factor cone interchange and literal target square."]
def diagram (X : Scheme.{u}ᵒᵖ) : Arrow (Arrow (Arrow (Arrow LoopPrespectrum.{w}))) :=
  F.mapArrow.mapArrow.mapArrow.mapArrow.obj (squareFunctor.mapArrow.mapArrow.obj (square X))

/-- The actual pointwise-cone target square supplied by generic double totalization. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeIndexTransport.lean:83"
  "adaptation" "Original independent-factor cone interchange and literal target square."]
def target (X : Scheme.{u}ᵒᵖ) : Arrow (Arrow LoopPrespectrum.{w}) :=
  coneSquare (Double.comparisonMap (diagram F X))


end KTheory.Bass.GeometricConeInterchange
