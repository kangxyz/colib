/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian

/-!
# Original cocartesian lifts in the covariant Grothendieck construction

The original pseudofunctor image supplies the lift object. The identity in that fiber supplies
the lift arrow. Its strong cocartesian universal property uses the actual composition comparison.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Bicategory
universe u v u' v'
namespace CategoryTheory.GrothendieckCocartesian
variable {C : Type u} [Category.{v} C]
  {F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'}}
  {R S : C} (x : F.obj ⟨R⟩) (f : R ⟶ S)

/-- The target is the actual image under the original pseudofunctor. -/
abbrev target : Pseudofunctor.Grothendieck F := ⟨S, (F.map f.toLoc).toFunctor.obj x⟩

/-- The original identity-fiber cocartesian lift. -/
abbrev lift : (⟨R, x⟩ : Pseudofunctor.Grothendieck F) ⟶ target x f := ⟨f, 𝟙 _⟩

instance instIsHomLift : (Pseudofunctor.Grothendieck.forget F).IsHomLift f (lift x f) :=
  IsHomLift.map _ (lift x f)

/-- The factorization through the lift uses the original inverse composition comparison. -/
abbrev factor {z : Pseudofunctor.Grothendieck F} (g : S ⟶ z.base)
    (φ : (⟨R, x⟩ : Pseudofunctor.Grothendieck F) ⟶ z)
    [hφ : (Pseudofunctor.Grothendieck.forget F).IsHomLift (f ≫ g) φ] : target x f ⟶ z where
  base := g
  fiber :=
    have h : φ.base = f ≫ g := by
      have h := IsHomLift.fac' (Pseudofunctor.Grothendieck.forget F) (f ≫ g) φ
      change φ.base = eqToHom (show R = R from rfl) ≫ (f ≫ g) ≫
        eqToHom (show z.base = z.base from rfl) at h
      simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h
    (F.mapComp f.toLoc g.toLoc).inv.toNatTrans.app x ≫ eqToHom (by simp [h]) ≫ φ.fiber

instance instIsHomLiftFactor {z : Pseudofunctor.Grothendieck F} (g : S ⟶ z.base)
    (φ : (⟨R, x⟩ : Pseudofunctor.Grothendieck F) ⟶ z)
    [hφ : (Pseudofunctor.Grothendieck.forget F).IsHomLift (f ≫ g) φ] :
    (Pseudofunctor.Grothendieck.forget F).IsHomLift g (factor x f g φ (hφ := hφ)) :=
  IsHomLift.map _ (factor x f g φ (hφ := hφ))

/-- The original factorization composes with the original lift to the supplied arrow. -/
theorem factor_fac {z : Pseudofunctor.Grothendieck F} (g : S ⟶ z.base)
    (φ : (⟨R, x⟩ : Pseudofunctor.Grothendieck F) ⟶ z)
    [hφ : (Pseudofunctor.Grothendieck.forget F).IsHomLift (f ≫ g) φ] :
    lift x f ≫ factor x f g φ (hφ := hφ) = φ := by
  have h := IsHomLift.fac (Pseudofunctor.Grothendieck.forget F) (f ≫ g) φ
  change f ≫ g = eqToHom (show R = R from rfl) ≫ φ.base ≫
    eqToHom (show z.base = z.base from rfl) at h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  rcases φ with ⟨k, φ⟩
  change f ≫ g = k at h
  subst k
  refine Pseudofunctor.Grothendieck.Hom.ext _ _ rfl ?_
  change (𝟙 _) ≫ (F.mapComp f.toLoc g.toLoc).hom.toNatTrans.app x ≫
    (F.map g.toLoc).toFunctor.map (𝟙 _) ≫
      (F.mapComp f.toLoc g.toLoc).inv.toNatTrans.app x ≫ (𝟙 _) ≫ φ = φ
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Functor.map_id, Category.id_comp,
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  exact Category.id_comp φ

/-- Every original identity-fiber lift is genuinely strongly cocartesian. -/
instance instIsStronglyCocartesian :
    (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian f (lift x f) where
  universal_property' {z} g φ hφ := by
    change (Pseudofunctor.Grothendieck.forget F).IsHomLift (f ≫ g) φ at hφ
    change S ⟶ z.base at g
    have := hφ
    refine ⟨factor x f g φ (hφ := hφ), ⟨instIsHomLiftFactor x f g φ (hφ := hφ), ?_⟩, ?_⟩
    · exact factor_fac x f g φ (hφ := hφ)
    rintro χ ⟨hχ, rfl⟩
    have := hχ
    obtain ⟨rfl⟩ : g = χ.base := by
      have h := @IsHomLift.fac _ _ _ _ (Pseudofunctor.Grothendieck.forget F)
        S z.base (target x f) z g χ hχ
      change g = eqToHom (show S = S from rfl) ≫ χ.base ≫
        eqToHom (show z.base = z.base from rfl) at h
      simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h
    ext <;> simp

end CategoryTheory.GrothendieckCocartesian
