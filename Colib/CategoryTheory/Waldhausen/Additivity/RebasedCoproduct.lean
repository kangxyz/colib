/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Additivity.CoproductFunctor
public import Colib.CategoryTheory.Waldhausen.ExactFunctorRebase

/-! # Canonical rebasing and unit isomorphisms of the coproduct

Adapted from `Quillen/Waldhausen/Additivity/CompactCoproductUnits.lean:27–55` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, coordinates and path concatenations are retained. -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u v

namespace CategoryTheory.Waldhausen.Additivity

open Product

variable {C : Type u} [Category.{v} C] (W : Structure C) [HasBinaryCoproducts C]

/-- The same canonically rebased coproduct functor used in the original based map. -/
def coproductRebasedFunctor : C × C ⥤ C :=
  CategoryTheory.rebaseFunctor coproductFunctor (productStructure W W).zero W.zero
    (((coproductFunctor_isExact W).zero (productStructure W W).isZero).iso W.isZero)

/-- Exactness uses the original coproduct witness and its actual canonical rebasing. -/
theorem coproductRebasedFunctor_exact :
    IsExact (productStructure W W).cof (productStructure W W).weq W.cof W.weq
      (coproductRebasedFunctor W) := (coproductFunctor_isExact W).rebase

/-- The original coproduct rebasing isomorphism, with its actual chosen-zero component. -/
def coproductRebaseIso : coproductFunctor ≅ coproductRebasedFunctor W :=
  CategoryTheory.rebaseFunctorIso coproductFunctor (productStructure W W).zero W.zero
    (((coproductFunctor_isExact W).zero (productStructure W W).isZero).iso W.isZero)

/-- The normalized coproduct sends the original pair of zeros exactly to the original zero. -/
theorem coproductRebasedFunctor_zero :
    (coproductRebasedFunctor W).obj (W.zero, W.zero) = W.zero :=
  CategoryTheory.rebaseFunctor_obj_base _ _ _ _

/-- Zero on the left uses the actual second coproduct embedding and its original unitor. -/
def coproductLeftUnitIso : secondEmbedding W ⋙ coproductRebasedFunctor W ≅ 𝟭 C :=
  isoWhiskerLeft (secondEmbedding W) (coproductRebaseIso W).symm ≪≫
    secondEmbeddingCoproductIso W

/-- Zero on the right uses the actual first coproduct embedding and its original unitor. -/
def coproductRightUnitIso : firstEmbedding W ⋙ coproductRebasedFunctor W ≅ 𝟭 C :=
  isoWhiskerLeft (firstEmbedding W) (coproductRebaseIso W).symm ≪≫
    firstEmbeddingCoproductIso W


end CategoryTheory.Waldhausen.Additivity
