/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.DegreeZero

/-! Regression consumers for actual projections and independent ordinary Ext universes. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite.Contraction
open AlgebraicGeometry.SheafWithTransfers
open Stacks.Cohomology.FreeYonedaUnivLE
universe w t v u

section GeneralSite
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

-- Neither the site-object universe nor the Ext universe is collapsed to coefficients.
example (F : Sheaf J AddCommGrpCat.{max v t}) {X Y : C} (f : X ⟶ Y) :
    IsIso ((cohomologyPresheaf.{w, t} F 0).map f.op) ↔ IsIso (F.obj.map f.op) :=
  zero_isIso_restriction_iff F f

-- Check the original canonical comparison on an actual restriction, not just an abstract iso.
example (F : Sheaf J AddCommGrpCat.{max v t}) {X Y : C} (f : X ⟶ Y)
    (x : (cohomologyPresheaf.{w, t} F 0).obj (op Y)) :
    extSectionsAddEquiv X F ((cohomologyPresheaf.{w, t} F 0).map f.op x) =
      F.obj.map f.op (extSectionsAddEquiv Y F x) :=
  extSectionsAddEquiv_naturality_left f F x
end GeneralSite

section Transfers
variable {k : Type u} [Field k]
  [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (F : SheafWithTransfers.{u + 1} k)

example : IsStrictA1Invariant F ↔ ∀ (n : ℕ) (X : SmoothSite (Spec (.of k))),
    IsIso ((cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) n).map
      ((projection (SmoothSite.additiveGroupObject (Spec (.of k)))).app X).op) :=
  isStrictA1Invariant_iff F

example : IsStrictA1Invariant F ↔ ∀ (n : ℕ) (X : SmoothSite (Spec (.of k))),
    IsIso ((cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) n).map
      (SmoothSite.productFst X (polynomialAffineLine (.of k))).op) :=
  isStrictA1Invariant_iff_polynomial_projection F

example (hF : IsStrictA1Invariant F) : F.obj.IsA1Invariant :=
  hF.isA1Invariant

example (hF : F.obj.IsA1Invariant) :
    A1.IsInvariant (.of k) (cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) 0) :=
  degreeZero_isInvariant F hF

example (hF : F.obj.IsA1Invariant) (X : SmoothSite (Spec (.of k))) :
    (degreeZeroProjectionIso F hF X).hom =
      (cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) 0).map
        ((projection (SmoothSite.additiveGroupObject (Spec (.of k)))).app X).op :=
  degreeZeroProjectionIso_hom F hF X

example (hF : F.obj.IsA1Invariant) (X : SmoothSite (Spec (.of k))) :
    (degreeZeroProjectionIso F hF X).inv =
      (cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) 0).map
        (nativeAffineSection (.of k) X 0).op :=
  degreeZeroProjectionIso_inv F hF X

example (hF : F.obj.IsA1Invariant) {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    (cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) 0).map
        (affineLineCylinder.map f).op ≫ (degreeZeroProjectionIso F hF X).inv =
      (degreeZeroProjectionIso F hF Y).inv ≫
        (cohomologyPresheaf.{w, u + 1} ((toSheaf k).obj F) 0).map f.op :=
  degreeZeroProjectionIso_inv_naturality F hF f
end Transfers

