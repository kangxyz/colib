/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.FiberedCategory.GrothendieckCocartesian
public import Colib.CategoryTheory.FiberedCategory.GrothendieckFiber

/-!
# Original fiber components of cocartesian arrows are invertible

The original identity-fiber lift factors a supplied cocartesian arrow through its actual fiber
component. Cocartesian cancellation and the identity base prove this component invertible.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Bicategory
universe u v u' v'
namespace CategoryTheory.GrothendieckCocartesian
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})

private theorem isIso_fiberHom {E : Type*} [Category* E] {π : E ⥤ C} {R : C}
    {a b : Functor.Fiber π R} (f : a ⟶ b) [IsIso f.val] : IsIso f := by
  have : π.IsHomLift (𝟙 R) f.val := f.property
  refine ⟨⟨⟨inv f.val, inferInstance⟩, ?_, ?_⟩⟩
  · apply Subtype.ext
    exact IsIso.hom_inv_id f.val
  · apply Subtype.ext
    exact IsIso.inv_hom_id f.val

attribute [local simp] PrelaxFunctor.map₂_eqToHom in
/-- The supplied original arrow factors through the original lift and its actual fiber map. -/
theorem lift_fiber {a b : Pseudofunctor.Grothendieck F} (φ : a ⟶ b) :
    lift a.fiber φ.base ≫ (GrothendieckFiber.inclusion F b.base).map φ.fiber = φ := by
  dsimp only [GrothendieckFiber.inclusion, lift, target]
  refine Pseudofunctor.Grothendieck.Hom.ext _ _ (by simp) ?_
  simp only [Quiver.Hom.id_toLoc, Cat.Hom.id_toFunctor, Functor.id_obj,
    Pseudofunctor.Grothendieck.categoryStruct_comp_base, Quiver.Hom.comp_toLoc,
    Pseudofunctor.Grothendieck.categoryStruct_comp_fiber, F.mapComp_id_right_hom_app,
    Strict.rightUnitor_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom,
    Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, Functor.map_id, Category.id_comp,
    Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  let h := congrArg (fun f : a.base ⟶ b.base => (F.map f.toLoc).toFunctor.obj a.fiber)
    (Category.comp_id φ.base)
  change eqToHom h.symm ≫ eqToHom h ≫ φ.fiber = φ.fiber
  exact (eqToHom_trans_assoc h.symm h φ.fiber).trans (Category.id_comp φ.fiber)

/-- Strong cocartesianness makes the original fiber component an actual isomorphism. -/
theorem isIso_fiber {a b : Pseudofunctor.Grothendieck F} (φ : a ⟶ b)
    [hφ : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian φ.base φ] :
    IsIso φ.fiber := by
  let ψ := (GrothendieckFiber.toFiber F b.base).map φ.fiber
  have hψ : (Pseudofunctor.Grothendieck.forget F).IsHomLift (𝟙 b.base) ψ.val := ψ.property
  have hcomp : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian
      (φ.base ≫ 𝟙 b.base) (lift a.fiber φ.base ≫ ψ.val) := by
    change (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian
      (φ.base ≫ 𝟙 b.base)
      (lift a.fiber φ.base ≫ (GrothendieckFiber.inclusion F b.base).map φ.fiber)
    rw [lift_fiber, Category.comp_id]
    exact hφ
  have : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian (𝟙 b.base) ψ.val :=
    @Functor.IsStronglyCocartesian.of_comp _ _ _ _
      (Pseudofunctor.Grothendieck.forget F) a.base b.base b.base a
      (target a.fiber φ.base) b φ.base (𝟙 b.base) (lift a.fiber φ.base) ψ.val
      (instIsStronglyCocartesian a.fiber φ.base) hcomp hψ
  have : IsIso ψ.val := Functor.IsStronglyCocartesian.isIso_of_base_isIso
    (Pseudofunctor.Grothendieck.forget F) (𝟙 b.base) ψ.val
  have : IsIso ψ := isIso_fiberHom ψ
  exact isIso_of_reflects_iso φ.fiber (GrothendieckFiber.toFiber F b.base)

end CategoryTheory.GrothendieckCocartesian
