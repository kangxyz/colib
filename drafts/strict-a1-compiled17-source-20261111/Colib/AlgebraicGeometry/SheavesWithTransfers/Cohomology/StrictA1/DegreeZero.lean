/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.Basic
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1ProjectionIso
public import Colib.CategoryTheory.Sites.Cohomology.DegreeZero

/-!
# The degree-zero base case of strict affine-line invariance

The canonical comparison of actual free-sheaf Ext in degree zero with sections
intertwines the literal projection maps. Consequently ordinary `H⁰` is homotopy
invariant exactly when the original sheaf with transfers is homotopy invariant.
Adapted from `Motivic/Cohomology/A1/StrictInvariance/DegreeZero.lean` at
motivic@a6805c4a87cdfd7717dd7a94039246a167f15380, blob
`8bcc6186e6ece037a08b6f6a22abc2d13ba6883c`.
The inverse is restriction along the actual zero section, naturally in both
the smooth object and the coefficient sheaf. No positive-degree invariance is
asserted, and the original coefficient universe is retained.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe w t v u

namespace AlgebraicGeometry.SheafWithTransfers
open Scheme Scheme.SmoothSite.Contraction
open Stacks.Cohomology.FreeYonedaUnivLE

variable {k : Type u} [Field k]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1})]

/-- The actual ordinary `H⁰` projection is invertible exactly when the original
graph-restricted sections projection is invertible. -/
theorem degreeZero_isIso_projection_iff (F : SheafWithTransfers.{u + 1} k)
    (X : SmoothSite (Spec (.of k))) :
    IsIso (A1.projectionPullback (.of k)
      (cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) 0) X) ↔
    IsIso (A1.projectionPullback (.of k)
      ((PresheafWithTransfers.toPresheaf k).obj F.obj) X) :=
  zero_isIso_restriction_iff _
    ((projection (SmoothSite.additiveGroupObject (Spec (.of k)))).app X)

/-- Homotopy invariance of the original transfer sheaf is exactly degree-zero
homotopy invariance for its actual ordinary cohomology. -/
theorem degreeZero_isInvariant_iff (F : SheafWithTransfers.{u + 1} k) :
    A1.IsInvariant (.of k)
      (cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) 0) ↔
      F.obj.IsA1Invariant :=
  forall_congr' (degreeZero_isIso_projection_iff F)

/-- The unconditional degree-zero base case: HI coefficients give HI ordinary `H⁰`. -/
theorem degreeZero_isInvariant (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) :
    A1.IsInvariant (.of k)
      (cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) 0) :=
  (degreeZero_isInvariant_iff F).mpr hF

/-- Strict affine-line invariance includes homotopy invariance of the original sections. -/
theorem IsStrictA1Invariant.isA1Invariant {F : SheafWithTransfers.{u + 1} k}
    (hF : F.IsStrictA1Invariant) : F.obj.IsA1Invariant :=
  (degreeZero_isInvariant_iff F).mp (hF 0)

/-- The actual degree-zero projection isomorphism for HI coefficients. -/
def degreeZeroProjectionIso (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (X : SmoothSite (Spec (.of k))) :
    (cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) 0).obj (op X) ≅
      (cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) 0).obj
        (op (affineLineCylinder.obj X)) :=
  A1.projectionIso (.of k) _ (degreeZero_isInvariant F hF) X

@[simp]
theorem degreeZeroProjectionIso_hom (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (X : SmoothSite (Spec (.of k))) :
    (degreeZeroProjectionIso F hF X).hom =
      (cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) 0).map
        ((projection (SmoothSite.additiveGroupObject (Spec (.of k)))).app X).op := rfl

/-- The inverse is restriction along the literal zero section. -/
theorem degreeZeroProjectionIso_inv (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) (X : SmoothSite (Spec (.of k))) :
    (degreeZeroProjectionIso F hF X).inv =
      (cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) 0).map
        (nativeAffineSection (.of k) X 0).op :=
  A1.projectionIso_inv (.of k) _ (degreeZero_isInvariant F hF) X 0

/-- The actual zero-section inverse is natural in every smooth-site morphism. -/
@[reassoc]
theorem degreeZeroProjectionIso_inv_naturality (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    (cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) 0).map
        (affineLineCylinder.map f).op ≫ (degreeZeroProjectionIso F hF X).inv =
      (degreeZeroProjectionIso F hF Y).inv ≫
        (cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) 0).map f.op :=
  A1.projectionIso_inv_naturality (.of k) _ (degreeZero_isInvariant F hF) f

/-- The actual zero-section inverse is natural in coefficient morphisms. -/
@[reassoc]
theorem degreeZeroProjectionIso_inv_coefficient_naturality
    {F G : SheafWithTransfers.{u + 1} k} (η : F ⟶ G)
    (hF : F.obj.IsA1Invariant) (hG : G.obj.IsA1Invariant)
    (X : SmoothSite (Spec (.of k))) :
    (degreeZeroProjectionIso F hF X).inv ≫
        ((cohomologyPresheafFunctor.{w, u + 1} _ 0).map
          ((toSheaf k).map η)).app (op X) =
      ((cohomologyPresheafFunctor.{w, u + 1} _ 0).map
          ((toSheaf k).map η)).app (op (affineLineCylinder.obj X)) ≫
        (degreeZeroProjectionIso G hG X).inv := by
  rw [degreeZeroProjectionIso_inv, degreeZeroProjectionIso_inv]
  exact ((cohomologyPresheafFunctor.{w, u + 1} _ 0).map
    ((toSheaf k).map η)).naturality (nativeAffineSection (.of k) X 0).op

end AlgebraicGeometry.SheafWithTransfers

