/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.DirectedUnion
public import Colib.Topology.FilteredRealization.CoconeWeakEquivalence
public import Mathlib.CategoryTheory.Sites.Point.Basic
import Colib.Topology.Realization.MorphismProperty

/-!
# Weakness of a directed union of simplicial subpresheaves

If the inclusion of a fixed subpresheaf is weak at each stage, the
actual inclusion into the directed union is weak on every site fiber.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.SimplicialSubpresheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Q : Cᵒᵖ ⥤ SSet.{max u v}}

/-- The comparison of the original inclusion with the colimit of its
stagewise factorizations uses the same section maps. -/
theorem isRealizationWeakEquivalence_homOfLE_iSup
    {I : Type (max u v)} [Preorder I] [IsFiltered I] (B : I → Subpresheaf Q) (hB : Monotone B)
    {A : Subpresheaf Q} (hA : ∀ i, A ≤ B i) (j₀ : I) (Φ : J.Point.{max u v})
    (h : ∀ i, SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map (homOfLE (hA i)))) :
    SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map (homOfLE
      ((hA j₀).trans (le_iSup B j₀)))) := by
  let E := Φ.presheafFiber (A := SSet.{max u v})
  let e : Cocone (diagram B hB ⋙ E) := E.mapCocone (iSupCocone B hB)
  have he : IsColimit e := isColimitOfPreserves E (isColimitISupCocone B hB)
  have hh {i j : I} (p : i ⟶ j) :
      homOfLE (hA i) ≫ homOfLE (hB (leOfHom p)) = homOfLE (hA j) := by
    apply (cancel_mono (inclusion (B j))).1
    simp only [Category.assoc, homOfLE_inclusion]
  have ht {i j : I} (p : i ⟶ j) :
      SSet.IsRealizationWeakEquivalence ((diagram B hB ⋙ E).map p) := by
    change SSet.IsRealizationWeakEquivalence (E.map (homOfLE (hB (leOfHom p))))
    have heq : E.map (homOfLE (hA i)) ≫ E.map (homOfLE (hB (leOfHom p))) =
        E.map (homOfLE (hA j)) := by
      rw [← E.map_comp, hh p]
    have hw : SSet.IsRealizationWeakEquivalence
        (E.map (homOfLE (hA i)) ≫ E.map (homOfLE (hB (leOfHom p)))) := by
      rw [heq]
      exact h j
    exact SSet.IsRealizationWeakEquivalence.of_comp_left hw (h i)
  have h₀ := Topology.FilteredRealization.isRealizationWeakEquivalence_coconeLeg
    (diagram B hB ⋙ E) e he ht j₀
  change SSet.IsRealizationWeakEquivalence (E.map (homOfLE (le_iSup B j₀))) at h₀
  have heq : E.map (homOfLE (hA j₀)) ≫ e.ι.app j₀ =
      E.map (homOfLE ((hA j₀).trans (le_iSup B j₀))) := by
    change E.map (homOfLE (hA j₀)) ≫ E.map (homOfLE (le_iSup B j₀)) = _
    rw [← E.map_comp]
    exact congrArg E.map ((cancel_mono (inclusion (⨆ i, B i))).1
      (by simp only [Category.assoc, homOfLE_inclusion]))
  rw [← heq]
  exact SSet.IsRealizationWeakEquivalence.comp h₀ (h j₀)

end CategoryTheory.SimplicialSubpresheaf
