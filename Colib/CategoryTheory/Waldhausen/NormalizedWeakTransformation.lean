/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExactFunctorRebase

/-! # Chosen-zero normalization of actual weak natural transformations

Implementation provenance: Quillen/Waldhausen/Functoriality/KMap.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd; extracted from native
KTheory/Waldhausen/Functoriality.lean without changing either proof.
Source-only; compilation remains pending.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {V : Structure C} {W : Structure D} {F G : C ⥤ D}

/-- Conjugate the actual transformation by the two canonical zero normalizations. -/
def normalizedWeakTransformation
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hG : IsExact V.cof V.weq W.cof W.weq G) (η : F ⟶ G) :
    CategoryTheory.rebaseFunctor F V.zero W.zero ((hF.zero V.isZero).iso W.isZero) ⟶
      CategoryTheory.rebaseFunctor G V.zero W.zero ((hG.zero V.isZero).iso W.isZero) :=
  (CategoryTheory.rebaseFunctorIso F V.zero W.zero ((hF.zero V.isZero).iso W.isZero)).inv ≫ η ≫
    (CategoryTheory.rebaseFunctorIso G V.zero W.zero ((hG.zero V.isZero).iso W.isZero)).hom

/-- Actual pointwise weakness survives this concrete conjugation. -/
theorem normalizedWeakTransformation_weak
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hG : IsExact V.cof V.weq W.cof W.weq G) (η : F ⟶ G)
    (hη : ∀ X, W.weq (η.app X)) (X : C) :
    W.weq ((normalizedWeakTransformation hF hG η).app X) :=
  W.weq.comp_mem _ _ (W.weq_iso _ inferInstance)
    (W.weq.comp_mem _ _ (hη X) (W.weq_iso _ inferInstance))

end CategoryTheory.Waldhausen
