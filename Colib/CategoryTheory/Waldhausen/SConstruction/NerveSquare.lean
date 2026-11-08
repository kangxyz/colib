/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveCylinderZero

/-! # Literal two-time nerve squares of commuting weak transformations

Horizontal time runs along the original top and bottom arrows; vertical time
runs along the original left and right components. Both parameters use only the
nerve coordinate. The square is a nested original cylinder, with no chosen
filler and with its four original edge cylinders retained exactly.
-/
/- Implementation provenance: `Waldhausen/SConstruction/NerveSquare.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original definitions, proofs,
independent parameters and all faces retained in native namespaces. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped Simplicial
universe v u
namespace CategoryTheory.Waldhausen
variable {D : Type u} [Category.{v} D] {n m : SimplexCategory}
variable {A B A' B' : Grid₂ n m ⥤ D}
variable (α : A ⟶ B) (α' : A' ⟶ B') (β : A ⟶ A') (δ : B ⟶ B')
variable (h : α ≫ δ = β ≫ α')

/-- The actual vertical transformation at the displayed horizontal nerve time. -/
def nerveSquareVertical (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram α τ ⟶ nerveCylinderDiagram α' τ :=
  whiskerLeft ((nerveTimeFunctor n τ).prod' (𝟭 (Grid₂ n m)))
    (Functor.uncurry.map (ComposableArrows.homMk₁
      (F := ComposableArrows.mk₁ α) (G := ComposableArrows.mk₁ α') β δ h))

/-- Each original vertical component is exactly the selected endpoint of the commuting square. -/
theorem nerveSquareVertical_app (τ : m ⟶ ⦋1⦌) (p : Grid₂ n m) :
    (nerveSquareVertical α α' β δ h τ).app p =
      ((ComposableArrows.homMk₁ (F := ComposableArrows.mk₁ α)
        (G := ComposableArrows.mk₁ α') β δ h).app (τ.toOrderHom p.1)).app p := rfl

/-- The original square has horizontal parameter τ and independent vertical parameter σ. -/
def nerveSquareDiagram (τ σ : m ⟶ ⦋1⦌) : Grid₂ n m ⥤ D :=
  nerveCylinderDiagram (nerveSquareVertical α α' β δ h τ) σ

/-- At vertical zero the square is the entire original α cylinder. -/
theorem nerveSquareDiagram_vertical_zero (τ : m ⟶ ⦋1⦌) :
    nerveSquareDiagram α α' β δ h τ (SimplexCategory.const m ⦋1⦌ 0) =
      nerveCylinderDiagram α τ := nerveCylinderDiagram_zero _

/-- At vertical one the square is the entire original α' cylinder. -/
theorem nerveSquareDiagram_vertical_one (τ : m ⟶ ⦋1⦌) :
    nerveSquareDiagram α α' β δ h τ (SimplexCategory.const m ⦋1⦌ 1) =
      nerveCylinderDiagram α' τ := nerveCylinderDiagram_one _

/-- At horizontal zero the square is the entire original β cylinder. -/
theorem nerveSquareDiagram_horizontal_zero (σ : m ⟶ ⦋1⦌) :
    nerveSquareDiagram α α' β δ h (SimplexCategory.const m ⦋1⦌ 0) σ =
      nerveCylinderDiagram β σ := by
  apply nerveCylinderDiagram_congr_app _ β
    (nerveCylinderDiagram_zero α) (nerveCylinderDiagram_zero α')
  intro p
  rfl

/-- At horizontal one the square is the entire original δ cylinder. -/
theorem nerveSquareDiagram_horizontal_one (σ : m ⟶ ⦋1⦌) :
    nerveSquareDiagram α α' β δ h (SimplexCategory.const m ⦋1⦌ 1) σ =
      nerveCylinderDiagram δ σ := by
  apply nerveCylinderDiagram_congr_app _ δ
    (nerveCylinderDiagram_one α) (nerveCylinderDiagram_one α')
  intro p
  rfl

/-- The selected actual vertical component is weak if the two original sides are weak. -/
theorem nerveSquareVertical_weak (W : Structure D)
    (hβ : ∀ p, W.weq (β.app p)) (hδ : ∀ p, W.weq (δ.app p))
    (τ : m ⟶ ⦋1⦌) (p : Grid₂ n m) :
    W.weq ((nerveSquareVertical α α' β δ h τ).app p) := by
  rw [nerveSquareVertical_app]
  have ht (t : Fin 2) : W.weq
      (((ComposableArrows.homMk₁ (F := ComposableArrows.mk₁ α)
        (G := ComposableArrows.mk₁ α') β δ h).app t).app p) := by
    fin_cases t
    · exact hβ p
    · exact hδ p
  exact ht (τ.toOrderHom p.1)

/-- Two actual cylinder constructions retain the four original S-grids and weak components. -/
theorem nerveSquareDiagram_isSimplex₂ (W : Structure D)
    (hα : ∀ p, W.weq (α.app p)) (hα' : ∀ p, W.weq (α'.app p))
    (hβ : ∀ p, W.weq (β.app p)) (hδ : ∀ p, W.weq (δ.app p))
    (hA : IsSimplex₂ W.cof W.weq A) (hB : IsSimplex₂ W.cof W.weq B)
    (hA' : IsSimplex₂ W.cof W.weq A') (hB' : IsSimplex₂ W.cof W.weq B')
    (τ σ : m ⟶ ⦋1⦌) : IsSimplex₂ W.cof W.weq (nerveSquareDiagram α α' β δ h τ σ) :=
  nerveCylinderDiagram_isSimplex₂ W _ (nerveSquareVertical_weak α α' β δ h W hβ hδ τ)
    (nerveCylinderDiagram_isSimplex₂ W α hα hA hB τ)
    (nerveCylinderDiagram_isSimplex₂ W α' hα' hA' hB' τ) σ

/-- Four actual zero corner diagrams make the entire two-time square constant. -/
theorem nerveSquareDiagram_eq_const_of_zero (Z : D) (hZ : IsZero Z)
    (hA : ∀ p, A.obj p = Z) (hB : ∀ p, B.obj p = Z)
    (hA' : ∀ p, A'.obj p = Z) (hB' : ∀ p, B'.obj p = Z)
    (τ σ : m ⟶ ⦋1⦌) :
    nerveSquareDiagram α α' β δ h τ σ = (Functor.const (Grid₂ n m)).obj Z := by
  apply nerveCylinderDiagram_eq_const_of_zero _ Z hZ
  · intro p
    exact congrArg (fun G : Grid₂ n m ⥤ D ↦ G.obj p)
      (nerveCylinderDiagram_eq_const_of_zero α Z hZ hA hB τ)
  · intro p
    exact congrArg (fun G : Grid₂ n m ⥤ D ↦ G.obj p)
      (nerveCylinderDiagram_eq_const_of_zero α' Z hZ hA' hB' τ)

end CategoryTheory.Waldhausen
