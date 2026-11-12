/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.PerfectFieldAssembly
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.FiniteFieldEpi
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.InfiniteFieldEpi
public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.Cylinder.DegreeOneGenericBaseZero
public import Colib.Util.References

/-! # Strict affine-line invariance over a perfect field

The ordinary Nisnevich cohomology of a homotopy-invariant sheaf with transfers
is invariant under the original affine-line projection in every degree.

Adapted from `Motivic/Cohomology/A1/StrictInvariance/PerfectField.lean` and
`Motivic/Cohomology/A1/LocalVanishing/RankZero/Vanishing.lean` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Over every perfect field, a homotopy-invariant Nisnevich sheaf with
transfers is strictly affine-line invariant for ordinary Nisnevich cohomology. -/
@[colib_tag "COL-1029", colib_ref "MVW2006" "Lecture 24, Theorem 24.1" "adaptation"
  "Ordinary Nisnevich cohomology of a homotopy-invariant transfer sheaf over a perfect field"]
theorem isStrictA1Invariant_of_perfect (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) : F.IsStrictA1Invariant := by
  have hEpi : Boundary.OriginalPresheaf.CanonicalBoundaryEpi k := by
    rcases finite_or_infinite k with hFinite | hInfinite
    · let := hFinite
      exact Boundary.OriginalPresheaf.canonicalBoundaryEpi_of_finite
    · let := hInfinite
      exact Boundary.OriginalPresheaf.canonicalBoundaryEpi
  refine isStrictA1Invariant_of_degreeOne_generic_and_boundary_epi hEpi ?_ F hF
  intro G hG
  dsimp only [WholeCylinderGenericOpenZero]
  intro Y _ _ s
  obtain ⟨V, _, hη, hz⟩ := SheafCohomology.exists_generic_base_cylinder_h_one_zero G hG Y s
  exact ⟨V, hη, hz⟩

/-- Strict affine-line invariance and coefficient homotopy invariance are
equivalent for Nisnevich sheaves with transfers over a perfect field. -/
@[colib_tag "COL-1029"]
theorem isStrictA1Invariant_iff_isA1Invariant_of_perfect (F : SheafWithTransfers.{u + 1} k) :
    F.IsStrictA1Invariant ↔ F.obj.IsA1Invariant :=
  ⟨fun h => h.isA1Invariant, isStrictA1Invariant_of_perfect F⟩

end AlgebraicGeometry.SheafWithTransfers
