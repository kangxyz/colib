/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.Waldhausen.Fibration.CofiberObjectChangeWeak
import Colib.CategoryTheory.Waldhausen.Fibration.BisimplexChangeWeak
import Colib.CategoryTheory.Waldhausen.SConstruction.WeakObjectCompositionPrism

/-! # Abstract categorical weak-object transport checks

These source-only examples retain independent object and hom universes, all three
composition faces, independent simplex operators, both pushout certificates and
whole functor/family equalities. Native elaboration has not been run.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open CategoryTheory.Waldhausen.Fibration
open scoped Simplicial
universe u v

section WeakArrows
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : W.weq f) (hg : W.weq g)

example : W.oneWeakArrow f hf =
    (⟨(oneEmbedding W).map f, (oneEmbedding_exact W).weak f hf⟩ :
      (⟨(oneEmbedding W).obj A⟩ : WeakRows W ⦋1⦌) ⟶ ⟨(oneEmbedding W).obj B⟩) := rfl

example : (W.weakObjectSimplex f hf).val =
    weakChainToGrid W (ComposableArrows.mk₁ (W.oneWeakArrow f hf)) := rfl

example : W.oneWeakArrow f hf ≫ W.oneWeakArrow g hg =
    W.oneWeakArrow (f ≫ g) (W.weq.comp_mem _ _ hf hg) :=
  W.oneWeakArrow_comp f g hf hg

example : W.weakObjectCompositionPrism f g hf hg =
    weakChainToGrid W (ComposableArrows.mk₂ (W.oneWeakArrow f hf) (W.oneWeakArrow g hg)) := rfl

example : IsSimplex₂ W.cof W.weq (W.weakObjectCompositionPrism f g hf hg) :=
  W.weakObjectCompositionPrism_isSimplex₂ f g hf hg

example : gridMap₂ (𝟙 ⦋1⦌) (SimplexCategory.δ 2) ⋙
      W.weakObjectCompositionPrism f g hf hg = (W.weakObjectSimplex f hf).val :=
  W.weakObjectCompositionPrism_first f g hf hg

example : gridMap₂ (𝟙 ⦋1⦌) (SimplexCategory.δ 0) ⋙
      W.weakObjectCompositionPrism f g hf hg = (W.weakObjectSimplex g hg).val :=
  W.weakObjectCompositionPrism_second f g hf hg

example : gridMap₂ (𝟙 ⦋1⦌) (SimplexCategory.δ 1) ⋙
      W.weakObjectCompositionPrism f g hf hg =
    (W.weakObjectSimplex (f ≫ g) (W.weq.comp_mem _ _ hf hg)).val :=
  W.weakObjectCompositionPrism_composite f g hf hg

-- The two directions of a mixed grid map remain actual row and nerve morphisms.
example {p q : Grid₂ ⦋1⦌ ⦋1⦌} (a : p ⟶ q) :
    (W.weakObjectSimplex f hf).val.map a =
      ((ComposableArrows.mk₁ (W.oneWeakArrow f hf)).obj p.1).obj.obj.map
          (homOfLE (leOfHom a).2) ≫
        ((ComposableArrows.mk₁ (W.oneWeakArrow f hf)).map
          (homOfLE (leOfHom a).1)).hom.hom.app q.2 := rfl
end WeakArrows

section Postcomposition
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D} {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

example (h0 : F.obj V.zero = W.zero) {A B : C} (f : A ⟶ B) (hf : V.weq f) :
    (V.weakObjectSimplex f hf).val ⋙ F =
      (W.weakObjectSimplex (F.map f) (hF.weak f hf)).val :=
  weakObjectSimplex_postcompose hF h0 f hf

example {n m : ℕ} (G : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C) (hG : IsSimplex₂ V.cof V.weq G) :
    bisimplexFamily V G hG ≫ sSetMap hF =
      bisimplexFamily W (G ⋙ F) (hG.postcomp V.cof V.weq hF) :=
  bisimplexFamily_postcompose hF G hG

example {n m n' m' : ℕ} (G : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C)
    (hG : IsSimplex₂ V.cof V.weq G)
    (α : ⦋n'⦌ ⟶ ⦋n⦌) (β : ⦋m'⦌ ⟶ ⦋m⦌) :
    (SSet.stdSimplex.map α ⊗ₘ SSet.stdSimplex.map β) ≫ bisimplexFamily V G hG =
      bisimplexFamily V (gridMap₂ α β ⋙ G) (hG.precomp V.cof V.weq α β) :=
  bisimplexFamily_precomp V G hG α β
end Postcomposition

section CofiberSimplex
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (V : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : V.cof i) (hQ : IsPushout i (0 : A ⟶ V.zero) q (0 : V.zero ⟶ Q))

example : V.cofiberObjectSimplex i q hi hQ =
    V.rowSimplex (cofiberTwoRow V i q hi hQ) := rfl

example : (V.cofiberObjectSimplex i q hi hQ).val =
    Structure.intervalProjection ⦋2⦌ ⋙
      cofiberTwoDiagram V i q (cofiberTwo_comp_eq_zero V i q hQ) := rfl

example (k : Fin 3) : (sSet V.cof V.weq).δ k (V.cofiberObjectSimplex i q hi hQ) =
    V.kZeroObjectSimplex (cofiberFaceObject (A := A) (B := B) (Q := Q) k) :=
  V.cofiberObjectSimplex_face i q hi hQ k

example (W : Structure C) (h0 : V.zero = W.zero) (hw : W.cof i)
    (hW : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) :
    (V.cofiberObjectSimplex i q hi hQ).val = (W.cofiberObjectSimplex i q hw hW).val :=
  cofiberObjectSimplex_val_of_zero_eq i q hi hQ W h0 hw hW

example (N : NestedWeakEquivalences V) (hi' : N.coarse.cof i)
    (hQ' : IsPushout i (0 : A ⟶ N.coarse.zero) q (0 : N.coarse.zero ⟶ Q)) :
    (sSetMap (changeWeak_exact N)).app (op ⦋2⦌) (V.cofiberObjectSimplex i q hi hQ) =
      N.coarse.cofiberObjectSimplex i q hi' hQ' :=
  cofiberObjectSimplex_changeWeak N i q hi hi' hQ hQ'

example (A : C) (W : Structure C) (h0 : V.zero = W.zero) :
    (V.cofiberObjectSimplex (𝟙 A) (0 : A ⟶ V.zero) (V.cof.id_mem A)
      (cofiberTwo_identity_square V)).val =
    (W.cofiberObjectSimplex (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
      (cofiberTwo_identity_square W)).val :=
  identityCofiberSimplex_val_of_zero_eq A W h0
end CofiberSimplex

section ChangeWeak
variable {C : Type u} [Category.{v} C] {V : Structure C}

example (N : NestedWeakEquivalences V) {n m : ℕ} (F : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C)
    (hF : IsSimplex₂ V.cof V.weq F) (hG : IsSimplex₂ N.coarse.cof N.coarse.weq F) :
    bisimplexFamily V F hF ≫ sSetMap (changeWeak_exact N) =
      bisimplexFamily N.coarse F hG :=
  bisimplexFamily_changeWeak N F hF hG

example (W : Structure C) (h0 : V.zero = W.zero)
    {A B : C} (f : A ⟶ B) (hf : V.weq f) (hg : W.weq f) :
    (V.weakObjectSimplex f hf).val = (W.weakObjectSimplex f hg).val :=
  weakObjectSimplex_val_of_zero_eq W h0 f hf hg
end ChangeWeak
