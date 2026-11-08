/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.IdentityCylinder
public import Colib.KTheory.Waldhausen.WeakNaturalTransformation

/-! # The entire original identity cylinder

Every actual cut of the original identity transformation retains its full grid, including
crossing morphisms. The original weak-grid cylinder therefore realizes to the original map
at every time, through the unchanged finite-cylinder inverse.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/IdentityCylinder.lean:93-112`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, universes,
normalizations, time coordinates and spatial boundaries are retained. -/
@[expose] public section
open Topology SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial Topology
universe u v w w'
namespace CategoryTheory.Waldhausen
variable {D : Type u} [Category.{v} D]

variable (W : Structure D) {X : SimplexCategoryᵒᵖ ⥤ SSet.{max u v}}
  (f : X ⟶ bisimplicialSSet W)

/-- Actual inverse-cylinder evaluation retains the same original map at every independent time. -/
theorem diagonalWeakGridIdentityHomotopy_realization (t : unitInterval)
    (x : |SSet.diagonalSSet X|) :
    realizationSimplicialHomotopy (diagonalWeakGridIdentityHomotopy W f) (t, x) =
      SSet.toTop.map (SSet.diagonalMap f) x := by
  have hp : (realizationCylinderIso (SSet.diagonalSSet X)).inv ≫
      SSet.toTop.map (CartesianMonoidalCategory.fst (SSet.diagonalSSet X) Δ[1]) =
        CartesianMonoidalCategory.fst _ _ := by
    rw [← realizationCylinderComparison_fst]
    change (realizationCylinderIso (SSet.diagonalSSet X)).inv ≫
      (realizationCylinderIso (SSet.diagonalSSet X)).hom ≫ _ = _
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change SSet.toTop.map (diagonalWeakGridIdentityHomotopy W f).h
    ((realizationCylinderIso (SSet.diagonalSSet X)).inv (x, ULift.up t)) = _
  rw [diagonalWeakGridIdentityHomotopy_cylinder, SSet.toTop.map_comp]
  change ((realizationCylinderIso (SSet.diagonalSSet X)).inv ≫
    SSet.toTop.map (CartesianMonoidalCategory.fst (SSet.diagonalSSet X) Δ[1]) ≫
      SSet.toTop.map (SSet.diagonalMap f)) (x, ULift.up t) = _
  rw [← Category.assoc, hp]
  rfl

end CategoryTheory.Waldhausen

attribute [colib_ref "quillen"
    "Quillen/Waldhausen/SConstruction/IdentityCylinder.lean:93-112"
    "adaptation"
    "Every input and time of the realized identity cylinder"]
  CategoryTheory.Waldhausen.diagonalWeakGridIdentityHomotopy_realization
