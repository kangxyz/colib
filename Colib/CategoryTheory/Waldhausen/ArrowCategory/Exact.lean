/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.ArrowCategory.Structure

/-! # Exact functors on the genuine arrow Waldhausen category

Implementation provenance: `Quillen/Waldhausen/ArrowCategory/Exact.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual component maps, exactness hypotheses and independent universes are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen
namespace ArrowCategory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) {F : C ⥤ D}

/-- An exact functor induces an exact functor on actual pointwise arrow structures. -/
theorem mapArrow_exact (hF : IsExact V.cof V.weq W.cof W.weq F) :
    IsExact (waldhausenStructure V).cof (waldhausenStructure V).weq
      (waldhausenStructure W).cof (waldhausenStructure W).weq F.mapArrow where
  zero h := isZero_of_components _ (hF.zero ((source_exact V).zero h))
    (hF.zero ((target_exact V).zero h))
  cofibration _ hf := ⟨hF.cofibration _ hf.1, hF.cofibration _ hf.2⟩
  weak _ hf := ⟨hF.weak _ hf.1, hF.weak _ hf.2⟩
  pushout hf h := isPushout_of_pointwise _ _ _ _
    (hF.pushout hf.1 (pointwise_of_isPushout V hf h).1)
    (hF.pushout hf.2 (pointwise_of_isPushout V hf h).2)
end ArrowCategory
end CategoryTheory.Waldhausen
