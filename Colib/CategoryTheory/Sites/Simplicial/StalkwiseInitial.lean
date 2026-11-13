/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseFibrantHom
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # The initial pointed object after stalkwise localization -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] (J : GrothendieckTopology C)

local notation "Q" => toStalkwiseHomotopyCategory C J

/-- The image of the one-point presheaf is initial if stalkwise fibrant
replacement exists. Every map into a fibrant target is represented by a
strict pointed map, and the strict map from the point is unique. -/
@[no_expose]
def isInitial_stalkwisePoint
    (hrep : ∀ X : PointedSimplicialPresheaf.{w} C,
      ∃ (Y : PointedSimplicialPresheaf.{w} C) (i : X ⟶ Y),
        stalkwiseTrivialMonomorphisms C J i ∧ IsStalkwiseInjectiveFibrant C J Y) :
    IsInitial ((Q).obj (point.{w} C)) := by
  classical
  have h (Y : StalkwiseHomotopyCategory.{w} C J) :
      ∃ f : (Q).obj (point.{w} C) ⟶ Y, ∀ g, g = f := by
    let X := (Q).objPreimage Y
    obtain ⟨Z, i, hi, hZ⟩ := hrep X
    have hi' : IsIso ((Q).map i) := isIso_toStalkwiseHomotopyCategory_map C i hi.2
    let e := ((Q).objObjPreimageIso Y).symm ≪≫ @asIso _ _ _ _ ((Q).map i) hi'
    refine ⟨(Q).map (fromPoint C Z) ≫ e.inv, fun g ↦ ?_⟩
    obtain ⟨f, hf⟩ := surjective_stalkwise_map_of_isStalkwiseInjectiveFibrant J hZ
      (point.{w} C) (g ≫ e.hom)
    change (Q).map f = g ≫ e.hom at hf
    have hpoint : f = fromPoint C Z := (point_isZero.{w} C).isInitial.hom_ext _ _
    rw [hpoint] at hf
    rw [hf, Category.assoc, e.hom_inv_id, Category.comp_id]
  exact IsInitial.ofUniqueHom (fun Y ↦ (h Y).choose) (fun Y ↦ (h Y).choose_spec)

end CategoryTheory.PointedSimplicialPresheaf
