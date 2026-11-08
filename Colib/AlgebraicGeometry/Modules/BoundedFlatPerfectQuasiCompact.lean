/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectReplacement
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectBoundedQuasiCompact

/-!
# Bounded Above Flat Perfect Replacements on Quasi-Compact Spaces

Quasi-compactness gives the cohomology upper bound needed by the actual native flat resolution.
The result has the original hypothesis `CompactSpace` only: no quasi-separatedness or
resolution property is needed. It is an actual object augmentation, not relative App2.

Adapted from `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/Replacement.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry StrictlyPerfect HomologicalComplex

universe u

namespace AlgebraicGeometry.RingedSpace

/-- Quasi-compactness supplies an honest cohomology upper bound for the original complex. -/
theorem IsPerfectComplex.exists_isLE {X : RingedSpace.{u, u}} [CompactSpace X.carrier]
    {K : CochainComplex (OXMod.{u, u, u} X) ℤ} (hK : IsPerfectComplex K) :
    ∃ b : ℤ, K.IsLE b := by
  let : HasDerivedCategory.{u + 1} (OXMod.{u, u, u} X) := HasDerivedCategory.standard _
  obtain ⟨b, hb⟩ := exists_isZero_homology_of_isPerfect (DerivedCategory.Q.obj K) hK.isPerfect
  refine ⟨b, (CochainComplex.isLE_iff K b).2 (fun n hn => ?_)⟩
  exact (exactAt_iff_isZero_homology K n).2
    ((hb n hn).of_iso ((DerivedCategory.homologyFunctorFactors _ n).app K).symm)

/-- Every native perfect complex on a quasi-compact space has an actual flat augmentation. -/
@[colib_tag "COL-0323",
  colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/Replacement.lean:53-63"
    "adaptation" "Actual bounded-above flat perfect replacement under quasi-compactness alone"]
theorem exists_boundedAboveFlatPerfectComplex_of_quasiCompact
    {X : RingedSpace.{u, u}} [CompactSpace X.carrier]
    (K : CochainComplex (OXMod.{u, u, u} X) ℤ) (hK : IsPerfectComplex K) :
    ∃ (P : CochainComplex (OXMod.{u, u, u} X) ℤ) (p : P ⟶ K),
      QuasiIso p ∧ boundedAboveFlatPerfectComplex X P := by
  obtain ⟨b, hb⟩ := hK.exists_isLE
  obtain ⟨P, p, hp, hP, -⟩ := exists_boundedAboveFlatPerfectComplex_of_isLE K hK b
  exact ⟨P, p, hp, hP⟩

end AlgebraicGeometry.RingedSpace
