/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Limits.PointedSmashFunctor
public import Colib.CategoryTheory.Sites.Simplicial.PointedPresheaf
import Colib.CategoryTheory.Limits.PointedSmashPreservation
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Monomorphisms of pointed simplicial presheaves under smash

A monomorphism of pointed sets admits a pointed retraction. Evaluation
compares the actual smash map with the smash map of the evaluated
factors, so the latter is a split monomorphism in every component.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

private theorem exists_pointedRetraction {X Y : Under (⊤_ (Type w))} (f : X ⟶ Y)
    [Mono f.right] : ∃ g : Y ⟶ X, f ≫ g = 𝟙 X := by
  let : Nonempty X.right := ⟨X.hom (terminal.from (PUnit : Type w) PUnit.unit)⟩
  let g : Y.right ⟶ X.right := ↾Function.invFun f.right
  have h : f.right ≫ g = 𝟙 X.right := by
    apply ConcreteCategory.hom_ext
    exact Function.leftInverse_invFun (CategoryTheory.injective_of_mono f.right)
  have hg : Y.hom ≫ g = X.hom := by
    rw [← Under.w f, Category.assoc, h, Category.comp_id]
  exact ⟨Under.homMk g hg, (Under.forget _).map_injective h⟩

variable {C : Type u} [Category.{v} C]

private abbrev degreeEvaluation (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    (Cᵒᵖ ⥤ SSet.{w}) ⥤ Type w :=
  (CategoryTheory.evaluation Cᵒᵖ SSet).obj U ⋙
    (CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type w)).obj n

/-- Smash preserves monomorphisms of both pointed simplicial presheaf factors. -/
theorem mono_smashMap {X X' Y Y' : PointedSimplicialPresheaf.{w} C} (f : X ⟶ X') (g : Y ⟶ Y')
    [Mono f] [Mono g] : Mono (Under.smashMap f g) := by
  let : Mono f.right := Under.mono_right_of_mono f
  let : Mono g.right := Under.mono_right_of_mono g
  suffices h : Mono (Under.smashMap f g).right from Under.mono_of_mono_right _
  refine (NatTrans.mono_iff_mono_app _).2 fun U ↦ (NatTrans.mono_iff_mono_app _).2 fun n ↦ ?_
  let F := degreeEvaluation.{w} U n
  let f' := (Under.mapPointed F).map f
  let g' := (Under.mapPointed F).map g
  let : Mono f'.right := preserves_mono_of_preservesLimit F f.right
  let : Mono g'.right := preserves_mono_of_preservesLimit F g.right
  obtain ⟨rf, hrf⟩ := exists_pointedRetraction f'
  obtain ⟨rg, hrg⟩ := exists_pointedRetraction g'
  have hr : (Under.smashMap f' g').right ≫ (Under.smashMap rf rg).right = 𝟙 _ := by
    rw [← Under.comp_right, Under.smashMap_comp, hrf, hrg, Under.smashMap_id, Under.id_right]
  let : Mono (Under.smashMap f' g').right := mono_of_mono_fac hr
  let e := Under.mapPointedSmashIso F X Y
  let e' := Under.mapPointedSmashIso F X' Y'
  have he : (Under.smashMap f' g').right ≫ e'.hom.right =
      e.hom.right ≫ F.map (Under.smashMap f g).right :=
    congrArg (fun h ↦ h.right) (Under.mapPointedSmashIso_naturality F f g)
  change Mono (F.map (Under.smashMap f g).right)
  have hmap : F.map (Under.smashMap f g).right =
      e.inv.right ≫ (Under.smashMap f' g').right ≫ e'.hom.right := by
    rw [he, Under.inv_right_hom_right_assoc]
  let : IsIso e.inv.right := (Under.forget _).map_isIso e.inv
  let : IsIso e'.hom.right := (Under.forget _).map_isIso e'.hom
  rw [hmap]
  infer_instance

/-- Smashing with a fixed pointed presheaf preserves monomorphisms. -/
theorem mono_smashRightFunctor_map (Y : PointedSimplicialPresheaf.{w} C)
    {X X' : PointedSimplicialPresheaf.{w} C} (f : X ⟶ X') [Mono f] :
    Mono ((Under.smashRightFunctor Y).map f) :=
  mono_smashMap f (𝟙 Y)

end CategoryTheory.PointedSimplicialPresheaf
