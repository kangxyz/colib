/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.EqToHom
/-!
# Explicit transport of natural isomorphisms along functor equalities

Source and target changes retain their equality morphisms. Their composition and identity
laws are proved before any application to concrete category presentations.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
universe u v u₁ v₁
namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
variable {F F' G G' H H' : C ⥤ D}

/-- Transport a natural isomorphism along the two specified functor equalities. -/
def transportIso (hF : F = F') (hG : G = G') (i : F' ≅ G') : F ≅ G :=
  eqToIso hF ≪≫ i ≪≫ eqToIso hG.symm

/-- The transported forward transformation retains both equality morphisms. -/
theorem transportIso_hom (hF : F = F') (hG : G = G') (i : F' ≅ G') :
    (transportIso hF hG i).hom = eqToHom hF ≫ i.hom ≫ eqToHom hG.symm := rfl

/-- Every transported component retains its source and target equality morphisms. -/
theorem transportIso_hom_app
    (hF : F = F') (hG : G = G') (i : F' ≅ G') (x : C) :
    (transportIso hF hG i).hom.app x =
      eqToHom (congrArg (fun K : C ⥤ D => K.obj x) hF) ≫ i.hom.app x ≫
        eqToHom (congrArg (fun K : C ⥤ D => K.obj x) hG.symm) := by
  simp only [transportIso_hom, NatTrans.comp_app, eqToHom_app]

/-- Transport cancels the common middle equality under composition. -/
theorem transportIso_trans
    (hF : F = F') (hG : G = G') (hH : H = H')
    (i : F' ≅ G') (j : G' ≅ H') :
    transportIso hF hH (i ≪≫ j) =
      transportIso hF hG i ≪≫ transportIso hG hH j := by
  subst F'; subst G'; subst H'
  ext x
  simp [transportIso]

/-- Transport of an identity comparison is the actual identity comparison. -/
theorem transportIso_refl (hF : F = F') :
    transportIso hF hF (Iso.refl F') = Iso.refl F := by
  subst F'
  ext x
  simp [transportIso]
end CategoryTheory.Functor
