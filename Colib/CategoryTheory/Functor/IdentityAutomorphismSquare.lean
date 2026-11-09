/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.Functor.IdentityAutomorphism

/-! Pointwise original identity actions retain their actual coefficient comparison square. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
namespace CategoryTheory.Functor.IdentityAutomorphism
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {H : Type u₄} [Category.{v₄} H]

/-- A strictly compatible identity action intertwines along the supplied original comparison. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Functor/IdentityAutomorphismSquare.lean:19-33"
  "adaptation" "Pointwise identity actions intertwine along the actual comparison"]
theorem onFunctor_whisker_square (F : C ⥤ D) (G : E ⥤ H) (a : C ⥤ E) (b : D ⥤ H)
    (η : F ⋙ b ⟶ a ⋙ G) (e : 𝟭 D ≅ 𝟭 D) (e' : 𝟭 H ≅ 𝟭 H)
    (he : Functor.whiskerRight e.hom b = Functor.whiskerLeft b e'.hom) :
    Functor.whiskerRight (onFunctor F e).hom b ≫ η =
      η ≫ Functor.whiskerLeft a (onFunctor G e').hom := by
  apply NatTrans.ext
  funext x
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    onFunctor_hom_app]
  have hx := congrArg (fun α ↦ α.app (F.obj x)) he
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app] at hx
  rw [hx]
  simpa only [Functor.id_map, Functor.id_obj, Functor.comp_obj] using
    (e'.hom.naturality (η.app x)).symm

end CategoryTheory.Functor.IdentityAutomorphism
