/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakGridSquare
public import Colib.Topology.Realization.DoubleCylinderSquare
public import Colib.KTheory.Waldhausen.WeakNaturalTransformation

/-! # Exact realized weak-grid squares and their full chosen-zero consumer

Both original continuous times are retained. Every edge is the actual old
weak-grid realization homotopy, and all four degenerate zero grids fix the whole square.
-/
/- Implementation provenance: `Waldhausen/SConstruction/WeakGridSquareRealization.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original definitions, proofs,
independent parameters and all faces retained in native namespaces. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

/-- The actual square keeps vertical time first, horizontal time second and original input last. -/
def diagonalWeakGridRealizationSquare :
    C(unitInterval × (unitInterval × |SSet.diagonalSSet X|),
      |SSet.diagonalSSet (bisimplicialSSet W)|) :=
  realizationDoubleCylinderSquare (weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ)

/-- Evaluation retains the two original finite-cylinder inverses without coordinate permutation. -/
theorem diagonalWeakGridRealizationSquare_apply (t s : unitInterval)
    (x : |SSet.diagonalSSet X|) :
    diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (t, (s, x)) =
      SSet.toTop.map (weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ)
        ((realizationCylinderIso (SSet.diagonalSSet X ⊗ Δ[1])).inv
          ((realizationCylinderIso (SSet.diagonalSSet X)).inv
            (x, ULift.up s), ULift.up t)) := rfl

/-- The whole vertical-zero edge is the original weak-grid realization homotopy. -/
theorem diagonalWeakGridRealizationSquare_vertical_zero (s : unitInterval)
    (x : |SSet.diagonalSSet X|) :
    diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (0, (s, x)) =
      diagonalWeakGridRealizationHomotopy W f00 f01 α hα hcompatα (s, x) :=
  realizationDoubleCylinderSquare_vertical_zero
    (weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ)
    (diagonalWeakGridHomotopy W f00 f01 α hα hcompatα)
    (weakGridFamilySquare_vertical_zero W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ) s x

/-- The whole vertical-one edge is the original weak-grid realization homotopy. -/
theorem diagonalWeakGridRealizationSquare_vertical_one (s : unitInterval)
    (x : |SSet.diagonalSSet X|) :
    diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (1, (s, x)) =
      diagonalWeakGridRealizationHomotopy W f10 f11 α' hα' hcompatα' (s, x) :=
  realizationDoubleCylinderSquare_vertical_one
    (weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ)
    (diagonalWeakGridHomotopy W f10 f11 α' hα' hcompatα')
    (weakGridFamilySquare_vertical_one W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ) s x

/-- The whole horizontal-zero edge is the original weak-grid realization homotopy. -/
theorem diagonalWeakGridRealizationSquare_horizontal_zero (t : unitInterval)
    (x : |SSet.diagonalSSet X|) :
    diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (t, (0, x)) =
      diagonalWeakGridRealizationHomotopy W f00 f10 β hβ hcompatβ (t, x) :=
  realizationDoubleCylinderSquare_horizontal_zero
    (weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ)
    (diagonalWeakGridHomotopy W f00 f10 β hβ hcompatβ)
    (weakGridFamilySquare_horizontal_zero W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ) t x

/-- The whole horizontal-one edge is the original weak-grid realization homotopy. -/
theorem diagonalWeakGridRealizationSquare_horizontal_one (t : unitInterval)
    (x : |SSet.diagonalSSet X|) :
    diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (t, (1, x)) =
      diagonalWeakGridRealizationHomotopy W f01 f11 δ hδ hcompatδ (t, x) :=
  realizationDoubleCylinderSquare_horizontal_one
    (weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ)
    (diagonalWeakGridHomotopy W f01 f11 δ hδ hcompatδ)
    (weakGridFamilySquare_horizontal_one W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ) t x

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
/-- The supplied four zero grids fix both independent times at the actual chosen zero vertex. -/
theorem diagonalWeakGridRealizationSquare_fixed_vertex (t s : unitInterval) :
    diagonalWeakGridRealizationSquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ (t, (s, realizationPoint x)) =
      realizationPoint (diagonalZeroVertex W) :=
  realizationDoubleCylinderSquare_fixed_vertex
    (weakGridFamilySquare W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ) x (diagonalZeroVertex W)
    (weakGridFamilySquare_fixed_vertex W f00 f01 f10 f11 α α' β δ h
      hα hα' hβ hδ hcompatα hcompatα' hcompatβ hcompatδ x hf00 hf01 hf10 hf11) t s

end CategoryTheory.Waldhausen
