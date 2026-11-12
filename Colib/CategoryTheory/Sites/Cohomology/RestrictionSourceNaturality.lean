/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Cohomology.RestrictionSource

/-! # Naturality of the original free sources for site restriction -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/CategoryTheory/Sites/RestrictionSourceNaturality.lean`,
blob `7673363d0e064b986125c35c2b0922c0d5bbd12d`.
The source, representing sections equivalence and identity generator are the pinned
Stacks FreeYonedaUnivLE objects. No legacy free source is defined.
Source candidate only; no elaboration result is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite
universe t v u u'
namespace Stacks.Cohomology.FreeYonedaUnivLE
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasSheafify K AddCommGrpCat.{max v t}]
  (G : C ⥤ D) [G.IsContinuous J K]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{max v t} J K).IsRightAdjoint]

/-- The canonical source map adjoint to the actual free-source isomorphism. -/
def restrictionSourceHom (X : C) : ((freeYoneda.{t} J).obj X) ⟶
    (G.sheafPushforwardContinuous AddCommGrpCat J K).obj (((freeYoneda.{t} K).obj (G.obj X))) :=
  (G.sheafAdjunctionContinuous AddCommGrpCat J K).homEquiv _ _
    (restrictionSourceIso J K G X).hom

/-- The canonical isomorphism intertwines the original section-representing equivalences. -/
theorem restrictionSourceIso_sections (X : C) (F : Sheaf K AddCommGrpCat.{max v t})
    (f : ((freeYoneda.{t} K).obj (G.obj X)) ⟶ F) :
    sectionsEquiv.{t} X _
      ((G.sheafAdjunctionContinuous AddCommGrpCat J K).homEquiv _ _
        ((restrictionSourceIso J K G X).hom ≫ f)) = sectionsEquiv.{t} (G.obj X) F f := by
  change (restrictedSectionsCorepresentable J K G X).homEquiv
    (((restrictedSectionsCorepresentable J K G X).uniqueUpToIso
      (sectionsCorepresentable K (G.obj X))).hom ≫ f) = _
  change (restrictedSectionsCorepresentable J K G X).homEquiv
    ((restrictedSectionsCorepresentable J K G X).homEquiv.symm
      ((sectionsCorepresentable K (G.obj X)).homEquiv (𝟙 _)) ≫ f) = _
  rw [Functor.CorepresentableBy.homEquiv_comp, Equiv.apply_symm_apply]
  exact ((sectionsCorepresentable K (G.obj X)).homEquiv_comp f (𝟙 _)).symm.trans
    (by simp only [Category.id_comp]; rfl)

/-- The canonical source map is the literal identity section under both representations. -/
theorem restrictionSourceHom_sections (X : C) :
    sectionsEquiv.{t} X _ (restrictionSourceHom J K G X) =
      sectionsEquiv.{t} (G.obj X) _ (𝟙 (((freeYoneda.{t} K).obj (G.obj X)))) := by
  simpa only [Category.comp_id, restrictionSourceHom] using restrictionSourceIso_sections J K G X _
    (𝟙 (((freeYoneda.{t} K).obj (G.obj X))))

/-- The original free-source map is natural in the site object. -/
theorem restrictionSourceHom_naturality {X Y : C} (f : X ⟶ Y) :
    (freeYoneda.{t} J).map f ≫ restrictionSourceHom J K G Y =
      restrictionSourceHom J K G X ≫
        (G.sheafPushforwardContinuous AddCommGrpCat J K).map
          ((freeYoneda.{t} K).map (G.map f)) := by
  apply (sectionsEquiv.{t} X _).injective
  rw [sectionsEquiv_naturality_left, restrictionSourceHom_sections,
    sectionsEquiv_naturality, restrictionSourceHom_sections]
  change _ = ((freeYoneda.{t} K).map (G.map f)).hom.app _
    (sectionsEquiv.{t} (G.obj X) _ (𝟙 _))
  rw [← sectionsEquiv_naturality, Category.id_comp,
    ← Category.comp_id ((freeYoneda.{t} K).map (G.map f)),
    sectionsEquiv_naturality_left]
  rfl

/-- The actual free-source isomorphism is natural, not merely an objectwise identification. -/
theorem restrictionSourceIso_naturality {X Y : C} (f : X ⟶ Y) :
    (G.sheafPullback AddCommGrpCat J K).map ((freeYoneda.{t} J).map f) ≫
        (restrictionSourceIso J K G Y).hom =
      (restrictionSourceIso J K G X).hom ≫
        (freeYoneda.{t} K).map (G.map f) := by
  apply ((G.sheafAdjunctionContinuous AddCommGrpCat J K).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  exact restrictionSourceHom_naturality J K G f

end Stacks.Cohomology.FreeYonedaUnivLE
