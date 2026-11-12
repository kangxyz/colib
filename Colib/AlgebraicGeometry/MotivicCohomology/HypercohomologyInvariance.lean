/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Hypercohomology
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Colib.AlgebraicGeometry.MotivicCohomology.CohomologySheafInvariance
import Colib.AlgebraicGeometry.Sites.Smooth.Injectives
import Colib.CategoryTheory.Sites.Hypercohomology.RestrictionBoundedAbove
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# Affine-line invariance of motivic hypercohomology

Over a perfect field, the ordinary cohomology of each cohomology sheaf of the
motivic complex is invariant under the affine-line projection. A common
projective dimension bound for the free representing sheaves of the scheme
and its affine-line cylinder therefore makes the actual motivic cohomology
pullback invertible in every integer degree.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Cohomology.FreeYonedaUnivLE

universe w u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
open SmoothSite.Contraction

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Pullback along the actual affine-line projection is invertible when both
free Nisnevich representing sheaves have projective dimension at most `d`. -/
theorem isIso_motivicCohomologyRestriction_affineLineProjection
    (p : ℤ) (q : ℕ) (X : SmoothSite (Spec (.of k))) (d : ℕ)
    [hX : HasProjectiveDimensionLE
      ((freeYoneda.{u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))).obj X) d]
    [hCylinder : HasProjectiveDimensionLE
      ((freeYoneda.{u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))).obj
        ((affineLineCylinder (S := Spec (.of k))).obj X)) d] :
    IsIso (motivicCohomologyRestriction k p q
      ((projection (SmoothSite.additiveGroupObject (Spec (.of k)))).app X)) := by
  let J := SmoothSite.nisnevichTopology (Spec (.of k))
  let : HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1}) :=
    hasExt_of_enoughInjectives _
  have hK : (motivicSheafComplex k q).IsLE (q : ℤ) :=
    ((motivicSheafComplex k q).isLE_iff (q : ℤ)).mpr (fun i hi ↦
      ((motivicSheafComplex k q).exactAt_iff_isZero_homology i).mpr
        (isZero_motivicSheafComplex_homology k q i hi))
  let X₁ := (affineLineCylinder (S := Spec (.of k))).obj X
  let : HasProjectiveDimensionLE ((freeYoneda.{u + 1} J).obj X) d := hX
  let : HasProjectiveDimensionLE ((freeYoneda.{u + 1} J).obj X₁) d := hCylinder
  exact isIso_hypercohomologyPresheaf_map_of_isLE J (X := X₁) (Y := X)
    ((projection (SmoothSite.additiveGroupObject (Spec (.of k)))).app X)
    d (motivicSheafComplex k q) (q : ℤ) hK
    (fun i n ↦ motivicSheafComplex_homology_cohomologyPresheaf_isA1Invariant k q i n X) p

end AlgebraicGeometry.PresheafWithTransfers
