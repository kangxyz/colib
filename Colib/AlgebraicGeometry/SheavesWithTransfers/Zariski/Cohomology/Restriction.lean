/-
Copyright (c) 2026 Colib contributors and Stacks contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.MapAlongCorepresentation
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact

/-!
# Cohomology for exact restriction of abelian sheaves

The exact restriction comparison of
`Stacks.Cohomology.BiggerSite.cohomologyPresheafRestrictionIso` extends to the original
`FreeYonedaUnivLE` cohomology presheaves. The coefficient universe can exceed
the site morphism universe. The map applies exact
restriction to extension classes and precomposes with the free-Yoneda unit.

Adapted from `Stacks@c496df0d9beea9deaeabcea8492605f9a0a2313b`,
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChangeOfTopology/CohomologyPresheafRestriction.lean`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open Stacks.Cohomology.ExtComparison

universe w t v u u'

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D) [G.IsContinuous J K]

set_option hygiene false in
set_option quotPrecheck false in
local notation "A" => AddCommGrpCat.{max v t}
local notation "R" => G.sheafPushforwardContinuous A J K

variable [HasSheafify J A] [HasSheafify K A]

private def restrictionUnit (U : C) :
    (freeYoneda.{t} J).obj U ⟶ (R).obj ((freeYoneda.{t} K).obj (G.obj U)) :=
  (sectionsEquiv.{t} U _).symm (sectionsEquiv.{t} (G.obj U) _ (𝟙 _))

private theorem sectionsEquiv_restrictionUnit (U : C) :
    sectionsEquiv.{t} U _ (restrictionUnit.{t} J K G U) =
      sectionsEquiv.{t} (G.obj U) _ (𝟙 _) :=
  Equiv.apply_symm_apply _ _

private theorem restrictionUnit_comp (U : C) (M : Sheaf K A)
    (f : (freeYoneda.{t} K).obj (G.obj U) ⟶ M) :
    sectionsEquiv.{t} U _ (restrictionUnit.{t} J K G U ≫ (R).map f) =
      sectionsEquiv.{t} (G.obj U) M f := by
  rw [sectionsEquiv_naturality, sectionsEquiv_restrictionUnit]
  exact (sectionsEquiv_naturality.{t} (G.obj U) (𝟙 _) f).symm.trans
    (congrArg _ (Category.id_comp f))

private theorem bijective_restrictionUnit_comp (U : C) (M : Sheaf K A) :
    Function.Bijective (fun f : (freeYoneda.{t} K).obj (G.obj U) ⟶ M ↦
      restrictionUnit.{t} J K G U ≫ (R).map f) := by
  have he : (fun f : (freeYoneda.{t} K).obj (G.obj U) ⟶ M ↦
      restrictionUnit.{t} J K G U ≫ (R).map f) =
      (sectionsEquiv.{t} U ((R).obj M)).symm ∘ sectionsEquiv.{t} (G.obj U) M := by
    funext f
    exact (Equiv.eq_symm_apply _).mpr (restrictionUnit_comp.{t} J K G U M f)
  rw [he]
  exact (Equiv.bijective _).comp (Equiv.bijective _)

private theorem restrictionUnit_naturality {U V : C} (g : V ⟶ U) :
    restrictionUnit.{t} J K G V ≫ (R).map ((freeYoneda.{t} K).map (G.map g)) =
      (freeYoneda.{t} J).map g ≫ restrictionUnit.{t} J K G U := by
  apply (sectionsEquiv.{t} V _).injective
  rw [restrictionUnit_comp, sectionsEquiv_naturality_left, sectionsEquiv_restrictionUnit]
  exact (congrArg _ (Category.comp_id _)).symm.trans
    (sectionsEquiv_naturality_left.{t} (G.map g) _ (𝟙 _))

variable [HasExt.{w} (Sheaf J A)] [HasExt.{w} (Sheaf K A)] [EnoughInjectives (Sheaf K A)]
  [PreservesFiniteLimits (G.sheafPushforwardContinuous A J K)]
  [PreservesFiniteColimits (G.sheafPushforwardContinuous A J K)]
  [(G.sheafPushforwardContinuous A J K).PreservesInjectiveObjects]

/-- When restriction is exact and preserves injectives, restricting the cohomology presheaf
agrees with the cohomology presheaf of the restricted sheaf. -/
@[no_expose]
def cohomologyPresheafFunctorRestrictionIso (n : ℕ) :
    cohomologyPresheafFunctor.{w, t} K n ⋙ (Functor.whiskeringLeft _ _ _).obj G.op ≅
      R ⋙ cohomologyPresheafFunctor.{w, t} J n := by
  refine NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun U ↦
    (AddEquiv.ofBijective (extMapAlong.{w, w} R (restrictionUnit.{t} J K G U.unop) F n)
      (extMapAlong_bijective R _ (bijective_restrictionUnit_comp.{t} J K G U.unop) F n)
    ).toAddCommGrpIso) ?_) ?_
  · intro U V g
    ext a
    exact extMapAlong_mk₀_comp R _ _ _ _ (restrictionUnit_naturality.{t} J K G g.unop) a
  · intro F F' f
    refine NatTrans.ext (funext fun U ↦ ?_)
    ext a
    exact extMapAlong_comp_mk₀ R (restrictionUnit.{t} J K G U.unop) f a

end Stacks.Cohomology.FreeYonedaUnivLE
