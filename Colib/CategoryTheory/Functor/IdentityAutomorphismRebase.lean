/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Functor.Rebase
public import Colib.CategoryTheory.Functor.IdentityAutomorphismNaturality
public import Colib.CategoryTheory.Functor.IdentityAutomorphismEvaluation

/-!
# Identity automorphisms under actual functor rebasing

The original object replacement and conjugated functor preserve the same supplied identity
automorphisms. All category, object and isomorphism data and the preservation hypothesis
are unchanged.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w u₁ v₁
open CategoryTheory
namespace CategoryTheory.Functor.IdentityAutomorphism
/-- The original rebased functor preserves the same identity action. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Functor/IdentityAutomorphismRebase.lean:28"
  "adaptation" "Original evaluation, chosen-zero normalization and unit transport"]
theorem rebase_preserves {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
    (F : C ⥤ D) (x : C) (y : D) (e : F.obj x ≅ y)
    (α : 𝟭 C ≅ 𝟭 C) (β : 𝟭 D ≅ 𝟭 D) (h : Preserves F α β) :
    Preserves (CategoryTheory.rebaseFunctor F x y e) α β :=
  map_hom_eq_of_iso (CategoryTheory.rebaseFunctor F x y e) F
    (CategoryTheory.rebaseFunctorIso F x y e).symm α β h


end CategoryTheory.Functor.IdentityAutomorphism
end
end
