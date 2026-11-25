/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.KTheory.Waldhausen.Iterated.ReferenceWhiskeringFamily
public import Colib.KTheory.Waldhausen.Iterated.SimplexProductDiagram

/-!
# Exact fixed columns in a common-reference product

A column retains the same reference and the actual fixed postcomposition.
Adapted from `ProductReferenceRows.lean` in Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen Topology
open SmallWaldhausenCategory

universe u v

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceProduct

/-- The literal product reference factors in the conventional composition order. -/
theorem composition_pair_iso {C D E : Type u}
    [Category.{v} C] [Category.{v} D] [Category.{v} E]
    {F₀ F₁ : C ⥤ D} {G₀ G₁ : D ⥤ E} (e : F₀ ≅ F₁) (f : G₀ ≅ G₁) :
    (Functor.uncurry.obj (whiskeringLeft C D E)).mapIso (e.prod f) =
      isoWhiskerRight e G₀ ≪≫ isoWhiskerLeft F₁ f := by
  apply Iso.ext
  rfl

section Functors

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {F₀ F₁ : C ⥤ D} {G₀ G₁ : D ⥤ E} (e : F₀ ≅ F₁) (f : G₀ ≅ G₁)

/-- The other actual product-composition order is the naturality square of f. -/
theorem composition_pair_iso_other :
    (Functor.uncurry.obj (whiskeringLeft C D E)).mapIso (e.prod f) =
      isoWhiskerLeft F₀ f ≪≫ isoWhiskerRight e G₁ := by
  apply Iso.ext
  ext X
  exact f.hom.naturality (e.hom.app X)



variable {H : C ⥤ E} (η : H ≅ F₀ ⋙ G₀)

theorem product_column_reference_iso :
    η ≪≫ (Functor.uncurry.obj (whiskeringLeft C D E)).mapIso (e.prod f) =
      (η ≪≫ isoWhiskerLeft F₀ f) ≪≫ isoWhiskerRight e G₁ := by
  rw [composition_pair_iso_other, Iso.trans_assoc]
/-- Fixing the left factor of the product retains the right family's original reference. -/
theorem product_row_reference_iso :
    η ≪≫ (Functor.uncurry.obj (whiskeringLeft C D E)).mapIso (e.prod f) =
      (η ≪≫ isoWhiskerRight e G₀) ≪≫ isoWhiskerLeft F₁ f := by
  rw [composition_pair_iso, Iso.trans_assoc]

end Functors

variable {V W T : WideSubcategory preservesZero.{u}} {p q : ℕ}
  (F : V ⟶ T) (F₀ : V ⟶ W) (Fs : Fin (p + 1) → (V ⟶ W))
  (ρ : ∀ i, F₀.hom.toFunctor ≅ (Fs i).hom.toFunctor)
  (G₀ : W ⟶ T) (Gs : Fin (q + 1) → (W ⟶ T))
  (σ : ∀ j, G₀.hom.toFunctor ≅ (Gs j).hom.toFunctor)
  (η : F.hom.toFunctor ≅ (F₀ ≫ G₀).hom.toFunctor)

/-- The exact old product reference, changed only by its supplied actual total normalization iso. -/
def reanchoredProductNode (i : Fin (SimplexGrid.dimension p q + 1)) :
    Σ J : V ⟶ T, F.hom.toFunctor ≅ J.hom.toFunctor :=
  ⟨CommonReferenceProduct.vertices Fs Gs i,
    η ≪≫ CommonReferenceProduct.references F₀ Fs ρ G₀ Gs σ i⟩

/-- Every fixed column retains the original first family after its literal fixed postcomposition. -/
theorem product_column_nodes (i : Fin (p + 1)) (j : Fin (q + 1)) :
    reanchoredProductNode F F₀ Fs ρ G₀ Gs σ η (SimplexGrid.index p q (i, j)) =
      ModelSimplex.postReferenceNode F (Gs j) (η ≪≫ isoWhiskerLeft F₀.hom.toFunctor (σ j))
        ⟨Fs i, ρ i⟩ := by
  unfold reanchoredProductNode CommonReferenceProduct.vertices CommonReferenceProduct.references
  rw [SimplexGrid.decode_index]
  dsimp only
  exact congrArg (fun ν : F.hom.toFunctor ≅ (Fs i ≫ Gs j).hom.toFunctor ↦
    (⟨Fs i ≫ Gs j, ν⟩ : Σ J : V ⟶ T, F.hom.toFunctor ≅ J.hom.toFunctor))
    (product_column_reference_iso (ρ i) (σ j) η)

/-- Every fixed row retains the exact second family after its original fixed precomposition. -/
theorem product_row_nodes (i : Fin (p + 1)) (j : Fin (q + 1)) :
    reanchoredProductNode F F₀ Fs ρ G₀ Gs σ η (SimplexGrid.index p q (i, j)) =
      ModelSimplex.preReferenceNode F (Fs i) (η ≪≫ isoWhiskerRight (ρ i) G₀.hom.toFunctor)
        ⟨Gs j, σ j⟩ := by
  unfold reanchoredProductNode CommonReferenceProduct.vertices CommonReferenceProduct.references
  rw [SimplexGrid.decode_index]
  dsimp only
  exact congrArg (fun ν : F.hom.toFunctor ≅ (Fs i ≫ Gs j).hom.toFunctor ↦
    (⟨Fs i ≫ Gs j, ν⟩ : Σ J : V ⟶ T, F.hom.toFunctor ≅ J.hom.toFunctor))
    (product_row_reference_iso (ρ i) (σ j) η)

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceProduct
