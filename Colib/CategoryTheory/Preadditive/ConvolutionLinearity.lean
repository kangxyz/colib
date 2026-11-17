/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Additivity forced by the convolution relations

For additive presheaves on a preadditive category with binary biproducts,
the two contravariant balancing relations force a bilinear pairing to be
additive in its morphism label. Only additivity in the first variable of
the indexing bifunctor is needed. No monoidal structure, topology, field,
or choice of a tensor model enters this argument.

This extracts the signed-label argument from transfer convolution.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w t

namespace CategoryTheory.Preadditive.Convolution

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable (F : C ⥤ C ⥤ C) [F.Additive]
variable {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} [P.Additive]
variable {X : C} {M : Type t} [AddCommGroup M]

/-- The two transfer relations already force addition in the correspondence label. -/
theorem pairing_add_hom
    (e : ∀ Y Z : C, (X ⟶ (F.obj Y).obj Z) → ((P.obj (op Y)) →+ (Q.obj (op Z)) →+ M))
    (he : ∀ {Y Y' Z Z' : C} (f : Y ⟶ Y') (g : Z ⟶ Z')
      (s : P.obj (op Y')) (t : Q.obj (op Z')) (a : X ⟶ (F.obj Y).obj Z),
      e Y Z a (P.map f.op s) (Q.map g.op t) =
        e Y' Z' (a ≫ ((F.map f).app Z ≫ (F.obj Y').map g)) s t)
    (Y Z : C) (a b : X ⟶ (F.obj Y).obj Z) (s : P.obj (op Y)) (t : Q.obj (op Z)) :
    e Y Z (a + b) s t = e Y Z a s t + e Y Z b s t := by
  let G := F.flip.obj Z
  let p₁ : (Y ⊞ Y) ⟶ Y := biprod.fst
  let p₂ : (Y ⊞ Y) ⟶ Y := biprod.snd
  let i₁ : Y ⟶ (Y ⊞ Y) := biprod.inl
  let i₂ : Y ⟶ (Y ⊞ Y) := biprod.inr
  let d : X ⟶ G.obj (Y ⊞ Y) := a ≫ G.map i₁ + b ≫ G.map i₂
  let : G.Additive :=
    { map_add := by
        intro A B f g
        change (F.map (f + g)).app Z = (F.map f).app Z + (F.map g).app Z
        exact NatTrans.congr_app (F.map_add (f := f) (g := g)) Z }
  have hp₁ : d ≫ G.map p₁ = a := by
    dsimp only [d]
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, ← G.map_comp, ← G.map_comp]
    simp only [i₁, i₂, p₁, biprod.inl_fst, biprod.inr_fst, G.map_id, G.map_zero,
      comp_zero, add_zero]
    exact Category.comp_id a
  have hp₂ : d ≫ G.map p₂ = b := by
    dsimp only [d]
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, ← G.map_comp, ← G.map_comp]
    simp only [i₁, i₂, p₂, biprod.inl_snd, biprod.inr_snd, G.map_id, G.map_zero,
      comp_zero, zero_add]
    exact Category.comp_id b
  have hp : d ≫ G.map (p₁ + p₂) = a + b := by
    rw [G.map_add, Preadditive.comp_add, hp₁, hp₂]
  have h (f : (Y ⊞ Y) ⟶ Y) :
      e (Y ⊞ Y) Z d (P.map f.op s) t = e Y Z (d ≫ G.map f) s t := by
    have hf := he f (𝟙 Z) s t d
    change e (Y ⊞ Y) Z d (P.map f.op s) (Q.map (𝟙 Z).op t) =
      e Y Z (d ≫ ((F.map f).app Z ≫ (F.obj Y).map (𝟙 Z))) s t at hf
    have hmap : (F.obj Y).map (𝟙 Z) = 𝟙 ((F.obj Y).obj Z) := (F.obj Y).map_id Z
    rw [hmap, Category.comp_id] at hf
    have ht : Q.map (𝟙 Z).op t = t := (ConcreteCategory.congr_hom (Q.map_id (op Z)) t)
    have h' := congrArg (fun z : Q.obj (op Z) => e (Y ⊞ Y) Z d (P.map f.op s) z) ht
    change e (Y ⊞ Y) Z d (P.map f.op s) t =
      e Y Z (d ≫ (F.map f).app Z) s t
    exact h'.symm.trans hf
  rw [← hp, ← h, op_add, P.map_add]
  change e (Y ⊞ Y) Z d (P.map p₁.op s + P.map p₂.op s) t = _
  rw [map_add]
  change e (Y ⊞ Y) Z d (P.map p₁.op s) t + e (Y ⊞ Y) Z d (P.map p₂.op s) t = _
  rw [h p₁, h p₂, hp₁, hp₂]

end CategoryTheory.Preadditive.Convolution
