/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.DirectedUnion
public import Mathlib.CategoryTheory.Limits.Types.Multicoequalizer
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Pushout of the intersection inclusions of simplicial subpresheaves

The pushout of the two literal inclusion maps out of the intersection is
the original union. This is the sectionwise pushout used to enlarge a
partially extended lift.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.SimplicialSubpresheaf

variable {C : Type u} [Category.{v} C] {P : Cᵒᵖ ⥤ SSet.{w}}

/-- A sectionwise union is the pushout of the inclusions of the intersection. -/
theorem isPushout_inf_sup (A B : Subpresheaf P) :
    IsPushout (homOfLE (inf_le_left : A ⊓ B ≤ A)) (homOfLE (inf_le_right : A ⊓ B ≤ B))
      (homOfLE (le_sup_left : A ≤ A ⊔ B)) (homOfLE (le_sup_right : B ≤ A ⊔ B)) := by
  have w : homOfLE (inf_le_left : A ⊓ B ≤ A) ≫ homOfLE (le_sup_left : A ≤ A ⊔ B) =
      homOfLE (inf_le_right : A ⊓ B ≤ B) ≫ homOfLE (le_sup_right : B ≤ A ⊔ B) := by
    apply (cancel_mono (inclusion (A ⊔ B))).1
    simp only [Category.assoc, homOfLE_inclusion]
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ w)
  apply evaluationJointlyReflectsColimits
  intro U
  apply evaluationJointlyReflectsColimits
  intro n
  let E := (CategoryTheory.evaluation Cᵒᵖ SSet.{w}).obj U ⋙
    (CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type w)).obj n
  let c := PushoutCocone.mk _ _ w
  change IsColimit (E.mapCocone c)
  apply (PushoutCocone.isColimitMapCoconeEquiv c E).2
  let q : Cᵒᵖ × SimplexCategoryᵒᵖ := (U, n)
  have h : Lattice.BicartSq ((A ⊓ B).obj q) (A.obj q) (B.obj q) ((A ⊔ B).obj q) :=
    { sup_eq := rfl, inf_eq := rfl }
  exact (Types.isPushout_of_bicartSq h).isColimit

end CategoryTheory.SimplicialSubpresheaf
