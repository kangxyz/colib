/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExactFunctorIso
public import Colib.CategoryTheory.Functor.Rebase

/-! # Exactness of chosen-zero rebasing

Implementation provenance: Quillen/Waldhausen/PointedFunctor.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd; extracted from native
KTheory/Waldhausen/CanonicalMap.lean with the same statement and proof.
Source-only; compilation remains pending.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe v u
namespace CategoryTheory.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {W' : Structure D}

/-- Exactness of the canonically rebased functor. -/
theorem IsExact.rebase {F : C ⥤ D} (hF : IsExact W.cof W.weq W'.cof W'.weq F) :
    IsExact W.cof W.weq W'.cof W'.weq
      (CategoryTheory.rebaseFunctor F W.zero W'.zero ((hF.zero W.isZero).iso W'.isZero)) :=
  hF.of_iso (CategoryTheory.rebaseFunctorIso F W.zero W'.zero ((hF.zero W.isZero).iso W'.isZero))

end CategoryTheory.Waldhausen
