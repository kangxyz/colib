/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Hypercohomology.Basic

/-!
# Signed shifts of unbounded hypercohomology

The comparison uses Mathlib's actual localization/shift isomorphism and
`shiftFunctorAdd`. Its components commute with the original restrictions
because those restrictions are precomposition by the native free-Yoneda maps.

Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/CategoryTheory/Sites/Hypercohomology/Shift.lean`.
No boundedness assumption or replacement complex is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- Localization preserves the original signed cochain shift and its addition law. -/
def hypercohomologyShiftTargetIso
    (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ) (q p : ℤ) :
    (DerivedCategory.Q.obj (K⟦q⟧))⟦p⟧ ≅ (DerivedCategory.Q.obj K)⟦q + p⟧ :=
  (shiftFunctor _ p).mapIso ((DerivedCategory.Q.commShiftIso q).app K) ≪≫
    (shiftFunctorAdd _ q p).symm.app (DerivedCategory.Q.obj K)

/-- The actual signed shift gives an additive comparison in every integer degree. -/
@[colib_tag "COL-0304"]
def hypercohomologyShiftAddEquiv
    (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ) (q p : ℤ) (X : C) :
    (hypercohomologyPresheaf J (K⟦q⟧) p).obj (op X) ≃+
      (hypercohomologyPresheaf J K (q + p)).obj (op X) :=
  ((preadditiveCoyoneda.obj (op
    ((DerivedCategory.singleFunctor _ 0).obj ((freeYoneda.{t} J).obj X)))).mapIso
      (hypercohomologyShiftTargetIso J K q p)).addCommGroupIsoToAddEquiv

/-- The shift comparison preserves every original geometric restriction. -/
@[colib_tag "COL-0304"]
theorem hypercohomologyShiftAddEquiv_restriction
    (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ) (q p : ℤ)
    {X Y : C} (f : X ⟶ Y) (x : (hypercohomologyPresheaf J (K⟦q⟧) p).obj (op Y)) :
    hypercohomologyShiftAddEquiv J K q p X
        ((hypercohomologyPresheaf J (K⟦q⟧) p).map f.op x) =
      (hypercohomologyPresheaf J K (q + p)).map f.op
        (hypercohomologyShiftAddEquiv J K q p Y x) := by
  change (_ ≫ x) ≫ (hypercohomologyShiftTargetIso J K q p).hom =
    _ ≫ x ≫ (hypercohomologyShiftTargetIso J K q p).hom
  exact Category.assoc (obj := DerivedCategory (Sheaf J AddCommGrpCat.{max v t})) _ _ _

/-- Shifting coefficients yields an isomorphism of actual hypercohomology presheaves. -/
@[colib_tag "COL-0304"]
def hypercohomologyShiftPresheafIso
    (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ) (q p : ℤ) :
    hypercohomologyPresheaf J (K⟦q⟧) p ≅ hypercohomologyPresheaf J K (q + p) :=
  NatIso.ofComponents
    (fun X ↦ (hypercohomologyShiftAddEquiv J K q p X.unop).toAddCommGrpIso) (by
      intro X Y f
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      exact hypercohomologyShiftAddEquiv_restriction J K q p f.unop x)

end Stacks.Cohomology.FreeYonedaUnivLE

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/CategoryTheory/Sites/Hypercohomology/Shift.lean"
  "adaptation"
  "Actual signed localization shifts and geometric restrictions in all integer degrees"]
  Stacks.Cohomology.FreeYonedaUnivLE.hypercohomologyShiftAddEquiv
  Stacks.Cohomology.FreeYonedaUnivLE.hypercohomologyShiftAddEquiv_restriction
  Stacks.Cohomology.FreeYonedaUnivLE.hypercohomologyShiftPresheafIso
