/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.Waldhausen.ExtensionCategory.HeterogeneousDetection

/-! Regression checks for actual relative cofibrations with distinct target universes. -/

noncomputable section

open CategoryTheory CategoryTheory.Waldhausen

universe u v u' v' u'' v'' w

variable {C : Type u} [Category.{v} C] (V : Structure C)

example {ι : Sort w} (D : ι → Type u') [∀ i, Category.{v'} (D i)]
    (W : ∀ i, Structure (D i)) (F : ∀ i, C ⥤ D i)
    (hF : ∀ i, IsExact V.cof V.weq (W i).cof (W i).weq (F i))
    (detect : ∀ ⦃A B : C⦄ (f : A ⟶ B), (∀ i, (W i).cof ((F i).map f)) → V.cof f)
    {X Y : ExtensionCategory.Obj V} {f : X ⟶ Y}
    (hf : ∀ i, ExtensionCategory.cof (W i)
      ((ExtensionCategory.postcompose V (W i) (hF i)).map f)) : ExtensionCategory.cof V f :=
  ExtensionCategory.cof_of_postcompose_heterogeneous V D W F hF detect hf

example {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]
    (W : Structure D) (U : Structure E) {F : C ⥤ D} {G : C ⥤ E}
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (detect : ∀ ⦃A B : C⦄ (f : A ⟶ B), W.cof (F.map f) → U.cof (G.map f) → V.cof f)
    {X Y : ExtensionCategory.Obj V} {f : X ⟶ Y}
    (hf : ExtensionCategory.cof W ((ExtensionCategory.postcompose V W hF).map f))
    (hg : ExtensionCategory.cof U ((ExtensionCategory.postcompose V U hG).map f)) :
    ExtensionCategory.cof V f :=
  ExtensionCategory.cof_of_postcompose_pair V W U hF hG detect hf hg
