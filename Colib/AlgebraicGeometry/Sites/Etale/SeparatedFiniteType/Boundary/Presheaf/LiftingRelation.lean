/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.Contraction.Representatives

/-! # Original signed restriction differences give genuine boundary equalities -/
/-!
Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/LiftingRelation.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `2af86fff9edf679235c0e18cfeeb9f5617105f75`. All generator and image-sieve maps use the
actual native Laurent cylinder and closed inverse-image boundary.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {B : Scheme.{u}} (P : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  {U Y Z : SmoothSite B} (j : U ⟶ Y) (i : Z ⟶ Y)

/-- The actual signed lift relation kills its ambient correction and preserves
restriction of the original punctured section, even when `P` is not a sheaf. -/
theorem presheafBoundaryGenerator_of_difference
    {W W' : EtaleSeparatedFiniteType Y.left} (f : W' ⟶ W)
    (s : ((baseChange j.left).op ⋙ (toSmoothSite U).op ⋙ P).obj (op W))
    (t : ((baseChange j.left).op ⋙ (toSmoothSite U).op ⋙ P).obj (op W'))
    (c : P.obj (op ((toSmoothSite Y).obj W')))
    (h : t - (presheafBoundaryRestriction P j).app (op W') c =
      ((baseChange j.left).op ⋙ (toSmoothSite U).op ⋙ P).map f.op s) :
    (presheafBoundaryGenerator P j i).app (op W') t =
      (presheafBoundary P j i).obj.map ((baseChange i.left).map f).op
        ((presheafBoundaryGenerator P j i).app (op W) s) := by
  have hmap := congrArg ((presheafBoundaryGenerator P j i).app (op W')) h
  rw [map_sub, presheafBoundaryGenerator_extend, sub_zero] at hmap
  exact hmap.trans (ConcreteCategory.congr_hom
    ((presheafBoundaryGenerator P j i).naturality f.op) s)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
