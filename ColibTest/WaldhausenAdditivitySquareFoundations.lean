/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Waldhausen.WeakGridSquareRealization
import Colib.KTheory.Waldhausen.WeakGridBasedHomotopy

/-! Regression obligations for the literal square, complete cylinder faces and two independent
realization times. Source-only: these examples have not been compiled. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory SSet
open scoped Simplicial Topology unitInterval
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


example (n : SimplexCategoryᵒᵖ)
    (z : ((SSet.diagonalSSet X ⊗ Δ[1]) ⊗ Δ[1]).obj n) :
    (((weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
    hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ).app n) z).1 =
      nerveSquareDiagram (α n n z.1.1) (α' n n z.1.1)
        (β n n z.1.1) (δ n n z.1.1) (h n n z.1.1) z.1.2.down z.2.down := rfl

example :
    SSet.ι₀ ≫ weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
        hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ =
      weakGridFamilyCylinder W f00 f01 α hα hcompatα :=
  weakGridFamilySquare_vertical_zero W f00 f01 f10 f11 α α' β δ h
    hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ

example :
    SSet.ι₁ ≫ weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
        hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ =
      weakGridFamilyCylinder W f10 f11 α' hα' hcompatα' :=
  weakGridFamilySquare_vertical_one W f00 f01 f10 f11 α α' β δ h
    hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ

example :
    (SSet.ι₀ ▷ Δ[1]) ≫ weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
        hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ =
      weakGridFamilyCylinder W f00 f10 β hβ hcompatβ :=
  weakGridFamilySquare_horizontal_zero W f00 f01 f10 f11 α α' β δ h
    hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ

example :
    (SSet.ι₁ ▷ Δ[1]) ≫ weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
        hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ =
      weakGridFamilyCylinder W f01 f11 δ hδ hcompatδ :=
  weakGridFamilySquare_horizontal_one W f00 f01 f10 f11 α α' β δ h
    hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ

example (t s : unitInterval)
    (x : |SSet.diagonalSSet X|) :
    diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (t, (s, x)) =
      SSet.toTop.map (weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ)
        ((realizationCylinderIso (SSet.diagonalSSet X ⊗ Δ[1])).inv
          ((realizationCylinderIso (SSet.diagonalSSet X)).inv
            (x, ULift.up s), ULift.up t)) :=
  diagonalWeakGridRealizationSquare_apply W f00 f01 f10 f11 α α' β δ h
    hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ t s x

example (s : unitInterval)
    (x : |SSet.diagonalSSet X|) :
    diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (0, (s, x)) =
      diagonalWeakGridRealizationHomotopy W f00 f01 α hα hcompatα (s, x) :=
  diagonalWeakGridRealizationSquare_vertical_zero W f00 f01 f10 f11 α α' β δ h
    hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ s x

example (s : unitInterval)
    (x : |SSet.diagonalSSet X|) :
    diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (1, (s, x)) =
      diagonalWeakGridRealizationHomotopy W f10 f11 α' hα' hcompatα' (s, x) :=
  diagonalWeakGridRealizationSquare_vertical_one W f00 f01 f10 f11 α α' β δ h
    hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ s x

example (t : unitInterval)
    (x : |SSet.diagonalSSet X|) :
    diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (t, (0, x)) =
      diagonalWeakGridRealizationHomotopy W f00 f10 β hβ hcompatβ (t, x) :=
  diagonalWeakGridRealizationSquare_horizontal_zero W f00 f01 f10 f11 α α' β δ h
    hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ t x

example (t : unitInterval)
    (x : |SSet.diagonalSSet X|) :
    diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (t, (1, x)) =
      diagonalWeakGridRealizationHomotopy W f01 f11 δ hδ hcompatδ (t, x) :=
  diagonalWeakGridRealizationSquare_horizontal_one W f00 f01 f10 f11 α α' β δ h
    hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ t x

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
example (t s : unitInterval) :
    diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (t, (s, realizationPoint x)) =
      realizationPoint (diagonalZeroVertex W) :=
  diagonalWeakGridRealizationSquare_fixed_vertex W f00 f01 f10 f11 α α' β δ h
    hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ x hf00 hf01 hf10 hf11 t s

end CategoryTheory.Waldhausen
