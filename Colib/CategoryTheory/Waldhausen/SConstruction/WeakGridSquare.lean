/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveSquareNaturality
public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakGridBasedHomotopy

/-! # Actual weak-grid squares with four unchanged cylinder faces

The supplied commuting natural transformations determine a literal two-time
nerve square. Each family keeps its own actual weak components and diagonal
reindexing law. All four old cylinders and the full chosen-zero square remain exact.
-/
/- Implementation provenance: `Waldhausen/SConstruction/WeakGridSquare.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original definitions, proofs,
independent parameters and all faces retained in native namespaces. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial
universe v u
namespace CategoryTheory.Waldhausen
variable {D : Type u} [Category.{v} D] (W : Structure D)
  {X : SimplexCategoryᵒᵖ ⥤ SSet.{max u v}}
  (f00 f01 f10 f11 : X ⟶ bisimplicialSSet W)
  (α : ∀ (n m : SimplexCategoryᵒᵖ) (x : (X.obj n).obj m),
    (((f00.app n).app m) x).1 ⟶ (((f01.app n).app m) x).1)
  (α' : ∀ (n m : SimplexCategoryᵒᵖ) (x : (X.obj n).obj m),
    (((f10.app n).app m) x).1 ⟶ (((f11.app n).app m) x).1)
  (β : ∀ (n m : SimplexCategoryᵒᵖ) (x : (X.obj n).obj m),
    (((f00.app n).app m) x).1 ⟶ (((f10.app n).app m) x).1)
  (δ : ∀ (n m : SimplexCategoryᵒᵖ) (x : (X.obj n).obj m),
    (((f01.app n).app m) x).1 ⟶ (((f11.app n).app m) x).1)
  (h : ∀ n m x, α n m x ≫ δ n m x = β n m x ≫ α' n m x)
  (hα : ∀ n m x p, W.weq ((α n m x).app p))
  (hα' : ∀ n m x p, W.weq ((α' n m x).app p))
  (hβ : ∀ n m x p, W.weq ((β n m x).app p))
  (hδ : ∀ n m x p, W.weq ((δ n m x).app p))
  (hcompatα : ∀ {n n' : SimplexCategoryᵒᵖ} (ρ : n ⟶ n')
    (x : (SSet.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop),
    HEq ((α n' n' ((SSet.diagonalSSet X).map ρ x)).app p)
      ((α n n x).app ((gridMap₂ ρ.unop ρ.unop).obj p)))
  (hcompatα' : ∀ {n n' : SimplexCategoryᵒᵖ} (ρ : n ⟶ n')
    (x : (SSet.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop),
    HEq ((α' n' n' ((SSet.diagonalSSet X).map ρ x)).app p)
      ((α' n n x).app ((gridMap₂ ρ.unop ρ.unop).obj p)))
  (hcompatβ : ∀ {n n' : SimplexCategoryᵒᵖ} (ρ : n ⟶ n')
    (x : (SSet.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop),
    HEq ((β n' n' ((SSet.diagonalSSet X).map ρ x)).app p)
      ((β n n x).app ((gridMap₂ ρ.unop ρ.unop).obj p)))
  (hcompatδ : ∀ {n n' : SimplexCategoryᵒᵖ} (ρ : n ⟶ n')
    (x : (SSet.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop),
    HEq ((δ n' n' ((SSet.diagonalSSet X).map ρ x)).app p)
      ((δ n n x).app ((gridMap₂ ρ.unop ρ.unop).obj p)))

/-- The literal square has horizontal inner time and independent vertical outer time. -/
def weakGridFamilySquare :
    (SSet.diagonalSSet X ⊗ Δ[1]) ⊗ Δ[1] ⟶
      SSet.diagonalSSet (bisimplicialSSet W) where
  app n := ↾fun z ↦ ⟨nerveSquareDiagram (α n n z.1.1) (α' n n z.1.1)
      (β n n z.1.1) (δ n n z.1.1) (h n n z.1.1) z.1.2.down z.2.down,
    nerveSquareDiagram_isSimplex₂ (α n n z.1.1) (α' n n z.1.1)
      (β n n z.1.1) (δ n n z.1.1) (h n n z.1.1) W
      (hα n n z.1.1) (hα' n n z.1.1) (hβ n n z.1.1) (hδ n n z.1.1)
      ((((f00.app n).app n) z.1.1).2) ((((f01.app n).app n) z.1.1).2)
      ((((f10.app n).app n) z.1.1).2) ((((f11.app n).app n) z.1.1).2)
      z.1.2.down z.2.down⟩
  naturality n n' ρ := by
    ext z
    apply Subtype.ext
    change nerveSquareDiagram (α n' n' ((SSet.diagonalSSet X).map ρ z.1.1))
      (α' n' n' ((SSet.diagonalSSet X).map ρ z.1.1))
      (β n' n' ((SSet.diagonalSSet X).map ρ z.1.1))
      (δ n' n' ((SSet.diagonalSSet X).map ρ z.1.1))
      (h n' n' ((SSet.diagonalSSet X).map ρ z.1.1))
      (ρ.unop ≫ z.1.2.down) (ρ.unop ≫ z.2.down) =
      gridMap₂ ρ.unop ρ.unop ⋙ nerveSquareDiagram (α n n z.1.1) (α' n n z.1.1)
        (β n n z.1.1) (δ n n z.1.1) (h n n z.1.1) z.1.2.down z.2.down
    exact (nerveSquareDiagram_congr_app _ _ _ _ _ _ _ _ _ _
      (diagonalGridMap_reindex W f00 ρ z.1.1) (diagonalGridMap_reindex W f01 ρ z.1.1)
      (diagonalGridMap_reindex W f10 ρ z.1.1) (diagonalGridMap_reindex W f11 ρ z.1.1)
      (hcompatα ρ z.1.1) (hcompatα' ρ z.1.1) (hcompatβ ρ z.1.1) (hcompatδ ρ z.1.1)
      (ρ.unop ≫ z.1.2.down) (ρ.unop ≫ z.2.down)).trans
      (nerveSquareDiagram_precomp (α n n z.1.1) (α' n n z.1.1)
        (β n n z.1.1) (δ n n z.1.1) (h n n z.1.1)
        ρ.unop ρ.unop z.1.2.down z.2.down)

/-- The whole vertical-zero face is its unchanged original weak-grid cylinder. -/
theorem weakGridFamilySquare_vertical_zero :
    SSet.ι₀ ≫ weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
        hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ =
      weakGridFamilyCylinder W f00 f01 α hα hcompatα := by
  ext n z
  apply Subtype.ext
  exact nerveSquareDiagram_vertical_zero (α n n z.1) (α' n n z.1)
    (β n n z.1) (δ n n z.1) (h n n z.1) z.2.down

/-- The whole vertical-one face is its unchanged original weak-grid cylinder. -/
theorem weakGridFamilySquare_vertical_one :
    SSet.ι₁ ≫ weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
        hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ =
      weakGridFamilyCylinder W f10 f11 α' hα' hcompatα' := by
  ext n z
  apply Subtype.ext
  exact nerveSquareDiagram_vertical_one (α n n z.1) (α' n n z.1)
    (β n n z.1) (δ n n z.1) (h n n z.1) z.2.down

/-- The whole horizontal-zero face is its unchanged original weak-grid cylinder. -/
theorem weakGridFamilySquare_horizontal_zero :
    (SSet.ι₀ ▷ Δ[1]) ≫ weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
        hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ =
      weakGridFamilyCylinder W f00 f10 β hβ hcompatβ := by
  ext n z
  apply Subtype.ext
  exact nerveSquareDiagram_horizontal_zero (α n n z.1) (α' n n z.1)
    (β n n z.1) (δ n n z.1) (h n n z.1) z.2.down

/-- The whole horizontal-one face is its unchanged original weak-grid cylinder. -/
theorem weakGridFamilySquare_horizontal_one :
    (SSet.ι₁ ▷ Δ[1]) ≫ weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
        hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ =
      weakGridFamilyCylinder W f01 f11 δ hδ hcompatδ := by
  ext n z
  apply Subtype.ext
  exact nerveSquareDiagram_horizontal_one (α n n z.1) (α' n n z.1)
    (β n n z.1) (δ n n z.1) (h n n z.1) z.2.down

variable (x : (SSet.diagonalSSet X) _⦋0⦌)
  (hf00 : ∀ (n : SimplexCategoryᵒᵖ) (z : (Δ[0] : SSet.{max u v}).obj n) p,
    ((((f00.app n).app n) ((SSet.yonedaEquiv.symm x).app n z)).1.obj p) = W.zero)
  (hf01 : ∀ (n : SimplexCategoryᵒᵖ) (z : (Δ[0] : SSet.{max u v}).obj n) p,
    ((((f01.app n).app n) ((SSet.yonedaEquiv.symm x).app n z)).1.obj p) = W.zero)
  (hf10 : ∀ (n : SimplexCategoryᵒᵖ) (z : (Δ[0] : SSet.{max u v}).obj n) p,
    ((((f10.app n).app n) ((SSet.yonedaEquiv.symm x).app n z)).1.obj p) = W.zero)
  (hf11 : ∀ (n : SimplexCategoryᵒᵖ) (z : (Δ[0] : SSet.{max u v}).obj n) p,
    ((((f11.app n).app n) ((SSet.yonedaEquiv.symm x).app n z)).1.obj p) = W.zero)

include hf00 hf01 hf10 hf11 in
/-- Four original zero grids force the complete double-cylinder vertex square to be constant. -/
theorem weakGridFamilySquare_fixed_vertex :
    ((SSet.yonedaEquiv.symm x ▷ Δ[1]) ▷ Δ[1]) ≫
        weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
        hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ =
      CartesianMonoidalCategory.fst (Δ[0] ⊗ Δ[1]) Δ[1] ≫
        CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
          SSet.yonedaEquiv.symm (diagonalZeroVertex W) := by
  ext n z
  apply Subtype.ext
  exact nerveSquareDiagram_eq_const_of_zero
    (α n n ((SSet.yonedaEquiv.symm x).app n z.1.1))
    (α' n n ((SSet.yonedaEquiv.symm x).app n z.1.1))
    (β n n ((SSet.yonedaEquiv.symm x).app n z.1.1))
    (δ n n ((SSet.yonedaEquiv.symm x).app n z.1.1))
    (h n n ((SSet.yonedaEquiv.symm x).app n z.1.1)) W.zero W.isZero
    (hf00 n z.1.1) (hf01 n z.1.1) (hf10 n z.1.1) (hf11 n z.1.1)
    z.1.2.down z.2.down

end CategoryTheory.Waldhausen
