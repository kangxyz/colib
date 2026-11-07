/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveSquare

/-! # Exact independent reindexing of the original two-time nerve square -/
/- Implementation provenance: `Waldhausen/SConstruction/NerveSquareNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original definitions, proofs,
independent parameters and all faces retained in native namespaces. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Opposite
open scoped Simplicial
universe v u
namespace CategoryTheory.Waldhausen
variable {D : Type u} [Category.{v} D] {n m : SimplexCategory}
variable {A B A' B' : Grid₂ n m ⥤ D}
variable (α : A ⟶ B) (α' : A' ⟶ B') (β : A ⟶ A') (δ : B ⟶ B')
variable (h : α ≫ δ = β ≫ α')

/-- Full endpoint and actual component equalities retain the entire original square. -/
theorem nerveSquareDiagram_congr_app {A₀ B₀ A₁ B₁ : Grid₂ n m ⥤ D}
    (α₀ : A₀ ⟶ B₀) (α₁ : A₁ ⟶ B₁) (β₀ : A₀ ⟶ A₁) (δ₀ : B₀ ⟶ B₁)
    (h₀ : α₀ ≫ δ₀ = β₀ ≫ α₁)
    (hA : A = A₀) (hB : B = B₀) (hA' : A' = A₁) (hB' : B' = B₁)
    (hα : ∀ p, HEq (α.app p) (α₀.app p))
    (hα' : ∀ p, HEq (α'.app p) (α₁.app p))
    (hβ : ∀ p, HEq (β.app p) (β₀.app p))
    (hδ : ∀ p, HEq (δ.app p) (δ₀.app p)) (τ σ : m ⟶ ⦋1⦌) :
    nerveSquareDiagram α α' β δ h τ σ = nerveSquareDiagram α₀ α₁ β₀ δ₀ h₀ τ σ := by
  subst A₀
  subst B₀
  subst A₁
  subst B₁
  have eα : α = α₀ := by ext p; exact eq_of_heq (hα p)
  have eα' : α' = α₁ := by ext p; exact eq_of_heq (hα' p)
  have eβ : β = β₀ := by ext p; exact eq_of_heq (hβ p)
  have eδ : δ = δ₀ := by ext p; exact eq_of_heq (hδ p)
  subst α₀
  subst α₁
  subst β₀
  subst δ₀
  rfl

include h in
/-- Reindex the given commutative square without choosing a new transformation. -/
theorem nerveSquare_reindex_comm {n' m' : SimplexCategory}
    (μ : n' ⟶ n) (ν : m' ⟶ m) :
    whiskerLeft (gridMap₂ μ ν) α ≫ whiskerLeft (gridMap₂ μ ν) δ =
      whiskerLeft (gridMap₂ μ ν) β ≫ whiskerLeft (gridMap₂ μ ν) α' := by
  simpa only [whiskerLeft_comp] using congrArg (whiskerLeft (gridMap₂ μ ν)) h

/-- Both original grid coordinates and both nerve times reindex independently. -/
theorem nerveSquareDiagram_precomp {n' m' : SimplexCategory}
    (μ : n' ⟶ n) (ν : m' ⟶ m) (τ σ : m ⟶ ⦋1⦌) :
    nerveSquareDiagram (whiskerLeft (gridMap₂ μ ν) α)
      (whiskerLeft (gridMap₂ μ ν) α') (whiskerLeft (gridMap₂ μ ν) β)
      (whiskerLeft (gridMap₂ μ ν) δ) (nerveSquare_reindex_comm α α' β δ h μ ν)
      (ν ≫ τ) (ν ≫ σ) = gridMap₂ μ ν ⋙ nerveSquareDiagram α α' β δ h τ σ := by
  change nerveCylinderDiagram _ (ν ≫ σ) = _
  trans nerveCylinderDiagram
    (whiskerLeft (gridMap₂ μ ν) (nerveSquareVertical α α' β δ h τ)) (ν ≫ σ)
  · apply nerveCylinderDiagram_congr_app _ _
      (nerveCylinderDiagram_precomp α μ ν τ) (nerveCylinderDiagram_precomp α' μ ν τ)
    intro p
    have ht (t : Fin 2) : HEq
        (((ComposableArrows.homMk₁
          (F := ComposableArrows.mk₁ (whiskerLeft (gridMap₂ μ ν) α))
          (G := ComposableArrows.mk₁ (whiskerLeft (gridMap₂ μ ν) α'))
          (whiskerLeft (gridMap₂ μ ν) β) (whiskerLeft (gridMap₂ μ ν) δ)
          (nerveSquare_reindex_comm α α' β δ h μ ν)).app t).app p)
        (((ComposableArrows.homMk₁ (F := ComposableArrows.mk₁ α)
          (G := ComposableArrows.mk₁ α') β δ h).app t).app ((gridMap₂ μ ν).obj p)) := by
      fin_cases t <;> rfl
    exact ht (τ.toOrderHom (ν.toOrderHom p.1))
  · exact nerveCylinderDiagram_precomp (nerveSquareVertical α α' β δ h τ) μ ν σ

end CategoryTheory.Waldhausen
