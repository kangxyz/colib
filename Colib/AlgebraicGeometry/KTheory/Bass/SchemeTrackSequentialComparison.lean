/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialDiagram
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialTransport

/-! Whole scheme naturality of the actual current-telescope to ordinary-colimit comparison. -/
/-!
Implementation provenance: adapted from Quillen at
`SchemeTrackSequentialComparison.lean` in its original source owner.
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

private theorem compose_squares {C : Type*} [Category* C] {S S' T T' U U' : C}
    (d : S ⟶ S') (e : T ⟶ T') (v : U ⟶ U')
    (a : S ⟶ T) (a' : S' ⟶ T') (b : T ⟶ U) (b' : T' ⟶ U')
    (h : d ≫ a' = a ≫ e) (k : e ≫ b' = b ≫ v) :
    d ≫ (a' ≫ b') = (a ≫ b) ≫ v := by
  rw [← Category.assoc, h, Category.assoc, k, ← Category.assoc]

/-- Every original scheme input commutes with the whole actual comparison map. -/
theorem comparison_naturality {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    (SchemeNaturalSeed.currentTelescope A).map g ≫ comparison M A Y =
      comparison M A X ≫ map M A g := by
  have hH : ∀ i n s x,
      (suspendedInput M g i).map n ((factorization M A X i).level n (s, x)) =
        (factorization M A Y i).level n (s, (input M g i).map n x) := by
    intro i n s x
    exact congrArg (fun h => h.map n x) (forward_input M A g i)
  have ht := ZigzagSequentialization.telescopeMap_naturality
    (vertex squareFunctor M X) (suspendedVertex squareFunctor M X)
    (forward M A X) (unit squareFunctor M X)
    (vertex squareFunctor M Y) (suspendedVertex squareFunctor M Y)
    (forward M A Y) (unit squareFunctor M Y)
    (input M g) (suspendedInput M g) (forward_input M A g) (unit_input M g)
    (current M A X) (current M A Y) (factorization M A X) (factorization M A Y)
    hH (fun i => (current_input M A g i).symm)
  have hc := ZigzagSequentialization.telescopeToOrdinaryColimit_naturality
    (vertex squareFunctor M X) (suspendedVertex squareFunctor M X)
    (forward M A X) (unit squareFunctor M X)
    (vertex squareFunctor M Y) (suspendedVertex squareFunctor M Y)
    (forward M A Y) (unit squareFunctor M Y)
    (input M g) (suspendedInput M g) (forward_input M A g) (unit_input M g)
  exact compose_squares _ _ _ _ _ _ _ ht hc

/-- The actual comparison is a natural transformation of the original scheme diagrams. -/
def comparisonNatTrans : SchemeNaturalSeed.currentTelescope A ⟶ diagram M A where
  app := comparison M A
  naturality {_X _Y} g := comparison_naturality M A g

/-- Retain the original source diagram under an equality of entire normalized tracks. -/
def comparisonNatTransOfEq
    (B : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (h : A = B) :
    SchemeNaturalSeed.currentTelescope A ⟶ diagram M B := by
  subst B
  exact comparisonNatTrans M A

/-- Each transported natural comparison is the already checked original component map. -/
theorem comparisonNatTransOfEq_app
    (B : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (h : A = B)
    (X : Scheme.{u}ᵒᵖ) :
    (comparisonNatTransOfEq M A B h).app X = comparisonOfEq M A B h X := by
  subst B
  rfl

end KTheory.Bass.SchemeTrackSequentialPresentation
