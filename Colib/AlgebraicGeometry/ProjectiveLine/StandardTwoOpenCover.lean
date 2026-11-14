/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceCharts.AffineOverBase
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper

/-!
# The standard two-open cover of the projective line

The cover is taken on Stacks' canonical relative projective space. Its overlap
is the inverse image open, with its actual two inclusion maps. This file does not
identify the standard opens with the chosen integral polynomial products.

See [Thomason–Trobaugh, §4][Thomason-Trobaugh1990], and compare
`Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/Native.lean`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace CategoryTheory
open Stacks.AlgebraicGeometry.ProjectiveSpaceCharts

namespace AlgebraicGeometry.Scheme.ProjectiveLine

universe u

variable (S : Scheme.{u})

/-- The zeroth standard coordinate open of the canonical projective line. -/
def positiveChart : (projectiveSpaceOver 1 S).Opens := coordChart 1 S 0

/-- The first standard coordinate open of the canonical projective line. -/
def negativeChart : (projectiveSpaceOver 1 S).Opens := coordChart 1 S 1

/-- The actual overlap as an open of the negative chart. -/
def chartOverlap : (negativeChart S).toScheme.Opens :=
  (negativeChart S).ι ⁻¹ᵁ positiveChart S

/-- The two standard coordinate opens cover the canonical projective line. -/
theorem standardChart_cover (x : projectiveSpaceOver 1 S) :
    x ∈ Set.range (negativeChart S).ι ∨ x ∈ positiveChart S := by
  have hx : x ∈ ⨆ i, coordChart 1 S i := by
    rw [iSup_coordChart_eq_top]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  fin_cases i
  · exact Or.inr hi
  · exact Or.inl ((Scheme.Opens.range_ι (negativeChart S)).ge hi)

instance [CompactSpace S] : CompactSpace (projectiveSpaceOver 1 S) :=
  QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceOver 1 S ↘ S)

instance [QuasiSeparatedSpace S] : QuasiSeparatedSpace (projectiveSpaceOver 1 S) :=
  quasiSeparatedSpace_of_quasiSeparated (projectiveSpaceOver 1 S ↘ S)

instance [CompactSpace S] : CompactSpace (positiveChart S).toScheme := by
  let : IsAffineHom ((positiveChart S).ι ≫ (projectiveSpaceOver 1 S ↘ S)) :=
    isAffineHom_coordChart_structureMorphism 1 S 0
  exact QuasiCompact.compactSpace_of_compactSpace
    ((positiveChart S).ι ≫ (projectiveSpaceOver 1 S ↘ S))

instance [CompactSpace S] : CompactSpace (negativeChart S).toScheme := by
  let : IsAffineHom ((negativeChart S).ι ≫ (projectiveSpaceOver 1 S ↘ S)) :=
    isAffineHom_coordChart_structureMorphism 1 S 1
  exact QuasiCompact.compactSpace_of_compactSpace
    ((negativeChart S).ι ≫ (projectiveSpaceOver 1 S ↘ S))

/-- Over a qcqs base the overlap of the two standard charts is compact. -/
theorem chartOverlap_isCompact [CompactSpace S] [QuasiSeparatedSpace S] :
    IsCompact (chartOverlap S : Set (negativeChart S).toScheme) :=
  (negativeChart S).ι.isCompact_preimage
    (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace (positiveChart S).toScheme))

end AlgebraicGeometry.Scheme.ProjectiveLine
