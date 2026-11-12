/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.CohomologySheaves
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.Basic
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.HomotopyInvariance
import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.HomotopyInvariance
import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.PerfectField
import Colib.Util.References

/-!
# Homotopy invariance of motivic cohomology sheaves

The actual transfer cohomology sheaves of the signed motivic complex are
affine-line invariant over every field. Over a perfect field, strict affine-line
invariance follows for their ordinary Nisnevich cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
open SmoothSite.Contraction
open Stacks.Cohomology.FreeYonedaUnivLE

variable (k : Type u) [Field k]

/-- Every transfer cohomology sheaf of the actual motivic complex is invariant
under the affine-line projection. -/
@[colib_tag "COL-1031"]
theorem motivicComplex_homology_isA1Invariant (q : ℕ) (i : ℤ) :
    ((motivicComplex k q).homology i).obj.IsA1Invariant := by
  let G := SheafWithTransfers.forget.{u + 1} k ⋙ toPresheaf.{u + 1} k
  by_cases hi : i ≤ (q : ℤ)
  · let r := ((q : ℤ) - i).toNat
    have hr : (q : ℤ) - r = i := by dsimp [r]; omega
    rw [← hr]
    let P := (singularComplex (reducedTorus k q)).homology r
    have hP := nisnevichSheafify_isA1Invariant P
      (singularComplex_homology_isA1Invariant (reducedTorus k q) r)
    let e := G.mapIso (motivicComplexHomologyIso k q r)
    intro X
    exact (NatIso.isIso_map_iff e
      ((projection (SmoothSite.additiveGroupObject (Spec (.of k)))).app X).op).2 (hP X)
  · have hZero := G.map_isZero (isZero_motivicComplex_homology k q i (lt_of_not_ge hi))
    have hX := (Functor.isZero_iff _).mp hZero
    intro X
    exact (hX _).isIso (hX _) _

variable [PerfectField k]
variable [HasExt.{u + 1}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Over a perfect field, each transfer cohomology sheaf of the actual motivic
complex is strictly affine-line invariant in ordinary Nisnevich cohomology. -/
@[colib_tag "COL-1031"]
theorem motivicComplex_homology_isStrictA1Invariant (q : ℕ) (i : ℤ) :
    ((motivicComplex k q).homology i).IsStrictA1Invariant :=
  SheafWithTransfers.isStrictA1Invariant_of_perfect _
    (motivicComplex_homology_isA1Invariant k q i)

/-- Ordinary Nisnevich cohomology of each cohomology sheaf of the actual ordinary
motivic complex is invariant under the affine-line projection over a perfect field. -/
@[colib_tag "COL-1031"]
theorem motivicSheafComplex_homology_cohomologyPresheaf_isA1Invariant
    (q : ℕ) (i : ℤ) (n : ℕ) :
    A1.IsInvariant (.of k)
      (cohomologyPresheaf.{u + 1, u + 1} ((motivicSheafComplex k q).homology i) n) := by
  let C := cohomologyPresheafFunctor.{u + 1, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) n
  let e := C.mapIso (motivicSheafComplexHomologyUnderlyingIso k q i)
  have h := (motivicComplex_homology_isStrictA1Invariant k q i) n
  intro X
  exact (NatIso.isIso_map_iff e
    ((projection (SmoothSite.additiveGroupObject (Spec (.of k)))).app X).op).2 (h X)

end AlgebraicGeometry.PresheafWithTransfers
