/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.FiberedCategory.GrothendieckCocartesianIso

/-!
# Strong transformations preserve the original Grothendieck cocartesian arrows

Invertibility of the actual fiber component is sufficient for strong cocartesianness, by
factorization through the original identity-fiber lift. The original Grothendieck map of a
strong transformation therefore preserves every such arrow, including its actual fiber map.
-/
/-! Adapted from
`Quillen/Aglib/CategoryTheory/FiberedCategory/GrothendieckCocartesianMap.lean`
at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory
universe u v u' v'
namespace CategoryTheory.GrothendieckCocartesian
variable {C : Type u} [Category.{v} C]
    {F G : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'}}

/-- An invertible actual fiber map makes the original arrow strongly cocartesian. -/
theorem of_isIso_fiber {a b : Pseudofunctor.Grothendieck F} (φ : a ⟶ b)
    [IsIso φ.fiber] :
    (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian φ.base φ := by
  let ψ := (GrothendieckFiber.toFiber F b.base).map φ.fiber
  have hψ : (Pseudofunctor.Grothendieck.forget F).IsHomLift (𝟙 b.base) ψ.val := ψ.property
  have : IsIso ψ.val := inferInstanceAs
    (IsIso ((GrothendieckFiber.inclusion F b.base).map φ.fiber))
  have hcomp : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian
      (φ.base ≫ 𝟙 b.base) (lift a.fiber φ.base ≫ ψ.val) := inferInstance
  change (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian
    (φ.base ≫ 𝟙 b.base)
    (lift a.fiber φ.base ≫ (GrothendieckFiber.inclusion F b.base).map φ.fiber) at hcomp
  simpa only [lift_fiber, Category.comp_id] using hcomp

/-- The unchanged Grothendieck map preserves every original strongly cocartesian arrow. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/FiberedCategory/GrothendieckCocartesianMap.lean:43"
  "adaptation" "Original actual objects, maps and proof on native infrastructure"]
theorem map_isStronglyCocartesian (α : Pseudofunctor.StrongTrans F G)
    {a b : Pseudofunctor.Grothendieck F} (φ : a ⟶ b)
    [(Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian φ.base φ] :
    (Pseudofunctor.Grothendieck.forget G).IsStronglyCocartesian φ.base
      ((Pseudofunctor.Grothendieck.map α).map φ) := by
  have : IsIso φ.fiber := isIso_fiber F φ
  have : IsIso (((Pseudofunctor.Grothendieck.map α).map φ).fiber) := by
    change IsIso ((α.naturality φ.base.toLoc).inv.toNatTrans.app a.fiber ≫
      (α.app ⟨b.base⟩).toFunctor.map φ.fiber)
    infer_instance
  exact of_isIso_fiber ((Pseudofunctor.Grothendieck.map α).map φ)

end CategoryTheory.GrothendieckCocartesian
