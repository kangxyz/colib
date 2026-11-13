/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.Subpresheaf
public import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Directed unions of simplicial subpresheaves

The lattice union is the colimit of the actual sectionwise inclusions.
Every site fiber therefore preserves a small directed union.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v u

namespace CategoryTheory.SimplicialSubpresheaf

variable {C : Type u} [Category.{v} C] {P : Cᵒᵖ ⥤ SSet.{w}}
  {I : Type t} [Preorder I] (A : I → Subpresheaf P) (hA : Monotone A)

@[simp]
theorem homOfLE_app_app {B D : Subpresheaf P} (h : B ≤ D) (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (s : B.obj (U, n)) : ((homOfLE h).app U).app n s = ⟨s.val, h _ s.property⟩ :=
  rfl

/-- The original inclusion maps between the stages of a monotone family. -/
def diagram : I ⥤ Cᵒᵖ ⥤ SSet.{w} where
  obj i := toPresheaf (A i)
  map f := homOfLE (hA (leOfHom f))
  map_id _ := (cancel_mono (inclusion _)).1 (by rw [homOfLE_inclusion, Category.id_comp])
  map_comp _ _ := (cancel_mono (inclusion _)).1 (by
    simp only [Category.assoc, homOfLE_inclusion])

/-- The inclusions into the actual sectionwise union. -/
def iSupCocone : Cocone (diagram A hA) where
  pt := toPresheaf (⨆ i, A i)
  ι.app i := homOfLE (le_iSup A i)
  ι.naturality i j f := (cancel_mono (inclusion (⨆ k, A k))).1 (by
    change (homOfLE (hA (leOfHom f)) ≫ homOfLE (le_iSup A j)) ≫ inclusion (⨆ k, A k) =
      (homOfLE (le_iSup A i) ≫ 𝟙 _) ≫ inclusion (⨆ k, A k)
    rw [Category.assoc, homOfLE_inclusion, homOfLE_inclusion, Category.comp_id, homOfLE_inclusion])

/-- The sectionwise union is the colimit of the original directed inclusions. -/
def isColimitISupCocone [IsFiltered I] : IsColimit (iSupCocone A hA) := by
  apply evaluationJointlyReflectsColimits
  intro U
  apply evaluationJointlyReflectsColimits
  intro n
  let c := ((CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type w)).obj n).mapCocone
    (((CategoryTheory.evaluation Cᵒᵖ SSet.{w}).obj U).mapCocone (iSupCocone A hA))
  change IsColimit c
  apply Types.FilteredColimit.isColimitOf' _ _
  · rintro ⟨s, hs⟩
    change s ∈ (⨆ i, A i).obj (U, n) at hs
    rw [Subfunctor.iSup_obj, Set.mem_iUnion] at hs
    obtain ⟨i, hi⟩ := hs
    exact ⟨i, ⟨s, hi⟩, rfl⟩
  · intro i s s' e
    have h : s.val = s'.val := by
      change (⟨s.val, _⟩ : (⨆ i, A i).obj (U, n)) = ⟨s'.val, _⟩ at e
      exact congrArg (fun x : (⨆ i, A i).obj (U, n) => x.val) e
    exact ⟨i, 𝟙 i, congrArg _ (Subtype.ext h)⟩

end CategoryTheory.SimplicialSubpresheaf
