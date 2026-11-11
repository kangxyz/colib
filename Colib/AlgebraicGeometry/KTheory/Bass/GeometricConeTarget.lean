/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeIndexTransport
public import Colib.CategoryTheory.ArrowSquareMapIso
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

variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
open GeometricSquareInterchange in
/-- The actual four unlooped factor isomorphisms between the two functor squares. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeTarget.lean:35"
  "adaptation" "Original four specified factor isomorphisms and literal total-cone target."]
def squareInterchange : geometricSquare (coneFunctor.obj F) ≅
    coneFunctor.mapArrow.mapArrow.obj (geometricSquare F) :=
  Arrow.squareMapIsoMk coneFunctor (geometricSquare F) (geometricSquare (coneFunctor.obj F))
    (Iso.refl _)
    (eta (polynomialProjection (.of (ULift.{u} ℤ))) F)
    (eta (polynomialProjection (.of (ULift.{u} ℤ))) F)
    (eta (laurentProjection (.of (ULift.{u} ℤ))) F)
    (id_comp_of_comp_eq (eta_projection (polynomialProjection (.of (ULift.{u} ℤ))) F))
    (id_comp_of_comp_eq (eta_projection (polynomialProjection (.of (ULift.{u} ℤ))) F))
    (eta_factor (laurentProjection (.of (ULift.{u} ℤ)))
      (polynomialProjection (.of (ULift.{u} ℤ))) (laurentToPolynomial (.of (ULift.{u} ℤ)))
      (laurentToPolynomial_projection (.of (ULift.{u} ℤ))) F).symm
    (eta_factor (laurentProjection (.of (ULift.{u} ℤ)))
      (polynomialProjection (.of (ULift.{u} ℤ))) (laurentMinus (.of (ULift.{u} ℤ)))
      (laurentMinus_projection (.of (ULift.{u} ℤ))) F).symm

/-- The literal pointwise target before applying the geometric factor isomorphisms. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeTarget.lean:52"
  "adaptation" "Original four specified factor isomorphisms and literal total-cone target."]
def componentTarget (X : Scheme.{u}ᵒᵖ) : Arrow (Arrow LoopPrespectrum.{w}) :=
  (SquareConeStrength.squareDiagram (coneFunctor.mapArrow.mapArrow.obj
    (GeometricSquareInterchange.geometricSquare F))).obj X

/-- Structural evaluation retains the original four comparison cones and all four maps. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeTarget.lean:57"
  "adaptation" "Original four specified factor isomorphisms and literal total-cone target."]
def targetComponentIso (X : Scheme.{u}ᵒᵖ) : target F X ≅ componentTarget F X := Iso.refl _

/-- Identify the actual target using the specified original independent-variable isomorphisms. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeTarget.lean:60"
  "adaptation" "Original four specified factor isomorphisms and literal total-cone target."]
def targetIso (X : Scheme.{u}ᵒᵖ) :
    (coneFunctor.obj F).mapArrow.mapArrow.obj (square X) ≅ target F X :=
  (((ArrowDiagrams.toDiagram.mapArrow ⋙ ArrowDiagrams.toDiagram).mapIso
    (squareInterchange F)).app X) ≪≫ (targetComponentIso F X).symm

/-- The original geometric double-cone permutation with its actual inverse target transports. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeTarget.lean:66"
  "adaptation" "Original four specified factor isomorphisms and literal total-cone target."]
def permutation (X : Scheme.{u}ᵒᵖ) :
    (coneFunctor.obj (coneFunctor.obj F)).obj X ≅ (coneFunctor.obj (coneFunctor.obj F)).obj X :=
  Double.interchangeIso (diagram F X) ≪≫ totalFunctor.mapIso (targetIso F X).symm

end KTheory.Bass.GeometricConeInterchange
