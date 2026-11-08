/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.Waldhausen.WeakArrow.DualDetection
import Colib.KTheory.Waldhausen.WeakArrow.KEquivalence
import Colib.KTheory.Waldhausen.WeakArrow.RelativeKEquivalence

/-! Regression tests for actual comma and weak-arrow objects, opposite detection,
relative map classes and the canonical chosen-zero KMap factorization. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v u' v' u'' v''

namespace CategoryTheory.Waldhausen.WeakArrow.Tests

section Structures

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
  (V : Structure C) (W : Structure D) (U : Structure E)
  (F : C ⥤ D) (G : D ⥤ E)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact W.cof W.weq U.cof U.weq G)

-- The category is literally the full subcategory on the original comma arrows.
example : Obj W F =
    ObjectProperty.FullSubcategory (fun X : Comma F (𝟭 D) => W.weq X.hom) := rfl

example (X : Obj W F) : W.weq X.obj.hom := X.property

-- A comma pushout is proved from the actual component universal properties.
example {A B E Q : FunctorComma.Obj F} (i : A ⟶ B) (f : A ⟶ E)
    (g : B ⟶ Q) (j : E ⟶ Q)
    (hC : IsPushout i.left f.left g.left j.left)
    (hFMap : IsPushout (F.map i.left) (F.map f.left) (F.map g.left) (F.map j.left))
    (hD : IsPushout i.right f.right g.right j.right) : IsPushout i f g j :=
  FunctorComma.isPushout_of_pointwise F i f g j hC hFMap hD

example (A : C) : ((diagonal W F).obj A).obj.hom = 𝟙 (F.obj A) := rfl

example : diagonal W F ⋙ source W F = 𝟭 C := diagonal_source W F

example : diagonal W F ⋙ target W F = F := diagonal_target W F

example (X : Obj W F) : ((counit W F).app X).hom.right = X.obj.hom := rfl

example (X : Obj W F) : (comparison W F).app X = X.obj.hom := rfl

example : IsExact (waldhausenStructure V W F hF).cof
    (waldhausenStructure V W F hF).weq V.cof V.weq (source W F) :=
  source_exact V W F hF

example : IsExact V.cof V.weq (waldhausenStructure V W F hF).cof
    (waldhausenStructure V W F hF).weq (diagonal W F) := diagonal_exact V W F hF

example {X Y : Obj W F} (f : X ⟶ Y) :
    (waldhausenStructure V W F hF).cof f ↔ V.cof f.hom.left ∧ W.cof f.hom.right := Iff.rfl

example [W.weq.HasTwoOutOfThreeProperty]
    (reflects : ∀ {A B : C} (f : A ⟶ B), W.weq (F.map f) → V.weq f)
    {X Y : Obj W F} (f : X ⟶ Y) (hf : W.weq ((target W F).map f)) :
    (waldhausenStructure V W F hF).weq f := target_reflects V W F hF reflects f hf

-- Relative structures preserve the actual objects, zero and cofibrations.
example : (Relative.arrowStructure V W U F G hF hG).zero =
    (waldhausenStructure V W F hF).zero := rfl

example : (Relative.arrowStructure V W U F G hF hG).cof =
    (waldhausenStructure V W F hF).cof := rfl

example {X Y : Obj W F} (f : X ⟶ Y) :
    (Relative.arrowStructure V W U F G hF hG).weq f ↔ U.weq (G.map f.hom.right) := Iff.rfl

example {A B : C} (f : A ⟶ B) :
    (Relative.sourceStructure V W U F G hF hG).weq f ↔
      U.weq (G.map (F.map f)) := Iff.rfl

example [U.weq.HasTwoOutOfThreeProperty] :
    IsExact (Relative.arrowStructure V W U F G hF hG).cof
      (Relative.arrowStructure V W U F G hF hG).weq
      (Relative.sourceStructure V W U F G hF hG).cof
      (Relative.sourceStructure V W U F G hF hG).weq (source W F) :=
  Relative.source_exact V W U F G hF hG

variable (Vd : Structure Cᵒᵖ) (Wd : Structure Dᵒᵖ)
  (hFd : IsExact Vd.cof Vd.weq Wd.cof Wd.weq F.op)
  (hV : IsCompatibleDual V Vd) (hW : IsCompatibleDual W Wd)

example {X Y : (Obj W F)ᵒᵖ} (f : X ⟶ Y) :
    (dualWaldhausenStructure V W Vd Wd F hF hFd hW).cof f ↔
      Vd.cof f.unop.hom.left.op ∧ Wd.cof f.unop.hom.right.op :=
  dual_cof_iff V W Vd Wd F hF hFd hW f

example {X Y : (Obj W F)ᵒᵖ} (f : X ⟶ Y) :
    (dualWaldhausenStructure V W Vd Wd F hF hFd hW).weq f ↔
      Vd.weq f.unop.hom.left.op ∧ Wd.weq f.unop.hom.right.op :=
  dual_weq_iff V W Vd Wd F hF hFd hW f

example : IsCompatibleDual (waldhausenStructure V W F hF)
    (dualWaldhausenStructure V W Vd Wd F hF hFd hW) :=
  dual_compatible V W Vd Wd F hF hFd hW hV

-- Detection of an arbitrary actual pushout has no cofibration or duality premise.
example {A B E Q : (Obj W F)ᵒᵖ} (i : A ⟶ B) (f : A ⟶ E) (g : B ⟶ Q) (j : E ⟶ Q)
    (hC : IsPushout ((source W F).op.map i) ((source W F).op.map f)
      ((source W F).op.map g) ((source W F).op.map j))
    (hD : IsPushout ((target W F).op.map i) ((target W F).op.map f)
      ((target W F).op.map g) ((target W F).op.map j)) : IsPushout i f g j :=
  dual_isPushout_of_components W F i f g j hC hD

example (X : (Obj W F)ᵒᵖ) (hC : IsZero ((source W F).op.obj X))
    (hD : IsZero ((target W F).op.obj X)) : IsZero X :=
  dual_isZero_of_components V W F hF X hC hD

example {A B : (Obj W F)ᵒᵖ} (s : BinaryCofan A B)
    (hC : IsColimit (BinaryCofan.mk ((source W F).op.map s.inl)
      ((source W F).op.map s.inr)))
    (hD : IsColimit (BinaryCofan.mk ((target W F).op.map s.inl)
      ((target W F).op.map s.inr))) : IsColimit s :=
  dualBinaryCofanIsColimitOfComponents V W F hF s hC hD

end Structures

section KMaps

variable {C D E : Type (max u v)} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  (V : Structure C) (W : Structure D) (U : Structure E)
  (F : C ⥤ D) (G : D ⥤ E)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact W.cof W.weq U.cof U.weq G)

example (n : ℕ) (x : V.K n) :
    diagonalKEquiv V W F hF n x = KMap (diagonal_exact V W F hF) n x := rfl

example (n : ℕ) (x : (waldhausenStructure V W F hF).K n) :
    (diagonalKEquiv V W F hF n).symm x = KMap (source_exact V W F hF) n x := rfl

example (n : ℕ) :
    (KMap (target_exact V W F hF) n).comp (diagonalKEquiv V W F hF n).toMonoidHom =
      KMap hF n := KMap_factor V W F hF n

example (n : ℕ) : KMap (target_exact V W F hF) n =
    (KMap hF n).comp (KMap (source_exact V W F hF) n) := KMap_target_eq V W F hF n

example (n : ℕ) : Function.Bijective (KMap hF n) ↔
    Function.Bijective (KMap (target_exact V W F hF) n) :=
  KMap_bijective_iff_target V W F hF n

variable [U.weq.HasTwoOutOfThreeProperty]

example (n : ℕ) (x : (Relative.sourceStructure V W U F G hF hG).K n) :
    Relative.diagonalKEquiv V W U F G hF hG n x =
      KMap (Relative.diagonal_exact V W U F G hF hG) n x := rfl

example (n : ℕ) :
    (KMap (Relative.target_exact V W U F G hF hG) n).comp
      (Relative.diagonalKEquiv V W U F G hF hG n).toMonoidHom =
      KMap (Relative.functor_exact V W U F G hF hG) n :=
  Relative.KMap_factor V W U F G hF hG n

example (n : ℕ) :
    Function.Bijective (KMap (Relative.functor_exact V W U F G hF hG) n) ↔
      Function.Bijective (KMap (Relative.target_exact V W U F G hF hG) n) :=
  Relative.KMap_bijective_iff_target V W U F G hF hG n

end KMaps
end CategoryTheory.Waldhausen.WeakArrow.Tests
