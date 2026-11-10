/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.SmallModelWhiskering

/-!
# Natural transformations with native model-arrow endpoints

Whiskering and equality transport retain the named native composite arrows in their
endpoint types. The projection equations identify these operations with the ordinary
functor operations; no comparison, zero or exactness hypothesis is added.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory
variable {U V W X Y : WideSubcategory preservesZero.{u}}

/-- Left whiskering with literal native composite endpoints. -/
def modelWhiskerLeft (E : U ⟶ V) {P Q : V ⟶ W}
    (μ : P.hom.toFunctor ⟶ Q.hom.toFunctor) :
    (E ≫ P).hom.toFunctor ⟶ (E ≫ Q).hom.toFunctor :=
  whiskerLeft E.hom.toFunctor μ

/-- The operation is ordinary left whiskering, with no additional transport. -/
theorem modelWhiskerLeft_eq (E : U ⟶ V) {P Q : V ⟶ W}
    (μ : P.hom.toFunctor ⟶ Q.hom.toFunctor) :
    modelWhiskerLeft E μ = whiskerLeft E.hom.toFunctor μ := rfl

/-- Right whiskering with explicitly right-associated native endpoints. -/
def modelWhiskerRightAssoc (A : U ⟶ V) (E : V ⟶ W)
    (B : U ⟶ X) (P : X ⟶ W) (Q : W ⟶ Y)
    (α : (A ≫ E).hom.toFunctor ⟶ (B ≫ P).hom.toFunctor) :
    (A ≫ (E ≫ Q)).hom.toFunctor ⟶ (B ≫ (P ≫ Q)).hom.toFunctor :=
  whiskerRight α Q.hom.toFunctor

/-- The association-aware operation is the original right whiskering. -/
theorem modelWhiskerRightAssoc_eq (A : U ⟶ V) (E : V ⟶ W)
    (B : U ⟶ X) (P : X ⟶ W) (Q : W ⟶ Y)
    (α : (A ≫ E).hom.toFunctor ⟶ (B ≫ P).hom.toFunctor) :
    modelWhiskerRightAssoc A E B P Q α = whiskerRight α Q.hom.toFunctor := rfl

/-- Equality transport between actual native model-arrow functors. -/
def modelEqToHom {F G : U ⟶ V} (h : F = G) : F.hom.toFunctor ⟶ G.hom.toFunctor :=
  eqToHom (congrArg (fun k : U ⟶ V => k.hom.toFunctor) h)

/-- The transport is precisely the original functor projection of the equality. -/
theorem modelEqToHom_eq {F G : U ⟶ V} (h : F = G) :
    modelEqToHom h = eqToHom (congrArg (fun k : U ⟶ V => k.hom.toFunctor) h) := rfl

/-- A right-unit comparison whiskered by a native arrow, with its actual target. -/
def modelWhiskerLeftId (E : U ⟶ V) {P : V ⟶ V}
    (δ : P.hom.toFunctor ⟶ (𝟙 V : V ⟶ V).hom.toFunctor) :
    (E ≫ P).hom.toFunctor ⟶ E.hom.toFunctor :=
  whiskerLeft E.hom.toFunctor δ

/-- The unit operation retains the literal original whiskered transformation. -/
theorem modelWhiskerLeftId_eq (E : U ⟶ V) {P : V ⟶ V}
    (δ : P.hom.toFunctor ⟶ (𝟙 V : V ⟶ V).hom.toFunctor) :
    modelWhiskerLeftId E δ = whiskerLeft E.hom.toFunctor δ := rfl

end CategoryTheory.Waldhausen.IteratedS
