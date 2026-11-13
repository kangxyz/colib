/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialInputLaws
public import Colib.Topology.Prespectrum.ZigzagSequentializationColimitNaturality

/-! Scheme functoriality of the actual ordinary pushout-colimit presentation. -/
/-!
Implementation provenance: adapted from `Quillen/KTheory/Bass/SchemeTrackSequentialDiagram.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole homotopies,
chosen nulls and proof terms are retained; namespaces and dependency owners are migrated.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u w
namespace KTheory.Bass.SchemeTrackSequentialPresentation
open NaturalTrack GeometricSeedCospan ModelZigzagSequentialization
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor))

/-- Original finite input maps induce the whole ordinary-colimit map. -/
def map {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) : presentation M A X ⟶ presentation M A Y :=
  ZigzagSequentialization.ordinaryColimitMap
    (vertex squareFunctor M X) (suspendedVertex squareFunctor M X)
    (forward M A X) (unit squareFunctor M X)
    (vertex squareFunctor M Y) (suspendedVertex squareFunctor M Y)
    (forward M A Y) (unit squareFunctor M Y)
    (input M g) (suspendedInput M g) (forward_input M A g) (unit_input M g)

/-- The actual colimit input map retains the identity. -/
theorem map_id (X : Scheme.{u}ᵒᵖ) : map M A (𝟙 X) = 𝟙 _ := by
  unfold map presentation
  simp only [show input M (𝟙 X) = fun i => 𝟙 _ from funext (input_id M X),
    show suspendedInput M (𝟙 X) = fun i => 𝟙 _ from funext (suspendedInput_id M X)]
  exact ZigzagSequentialization.ordinaryColimitMap_id _ _ _ _

/-- The actual colimit input map retains composition of original scheme maps. -/
theorem map_comp {X Y Z : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map M A (f ≫ g) = map M A f ≫ map M A g := by
  unfold map presentation
  rw [ZigzagSequentialization.ordinaryColimitMap_comp]
  congr 1
  · exact funext (input_comp M f g)
  · exact funext (suspendedInput_comp M f g)

/-- The prescribed ordinary-colimit presentations form an actual scheme diagram. -/
def diagram : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w} where
  obj := presentation M A
  map := map M A
  map_id := map_id M A
  map_comp := map_comp M A

end KTheory.Bass.SchemeTrackSequentialPresentation
