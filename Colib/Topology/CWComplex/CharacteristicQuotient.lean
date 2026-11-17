/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.CompactOpen
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# The actual characteristic quotient of a classical CW complex

The domain is the coproduct of the literal characteristic closed disks.
Hausdorffness is explicit:
it turns compact characteristic images into closed subsets of the ambient space.
The target is the actual subspace, not the ambient space.

Adapted from `Quillen/Topology/CWComplex/CharacteristicQuotient.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

open Topology
noncomputable section
open Set Metric
open scoped unitInterval
universe u v
namespace Topology.CWComplex
variable {X : Type u} [TopologicalSpace X] (C : Set X) [CWComplex C]

/-- The sup-norm closed disk appearing in Mathlib's classical characteristic maps. -/
abbrev CharacteristicDisk (n : ℕ) :=
  ↥(closedBall (0 : Fin n → ℝ) 1)

/-- The actual coproduct of all characteristic closed disks. -/
abbrev CharacteristicDomain := Σ n : ℕ, Σ _ : RelCWComplex.cell C n, CharacteristicDisk n

/-- The original characteristic map, with its range restricted to the actual complex. -/
def characteristicQuotient : CharacteristicDomain C → C := fun ⟨n, i, z⟩ =>
  ⟨RelCWComplex.map n i z,
    CWComplex.closedCell_subset_complex n i ⟨z, z.property, rfl⟩⟩

/-- The sum of the original characteristic maps is continuous. -/
theorem continuous_characteristicQuotient : Continuous (characteristicQuotient C) := by
  apply continuous_sigma
  intro n
  apply continuous_sigma
  intro i
  exact (continuousOn_iff_continuous_domRestrict.mp (RelCWComplex.continuousOn n i)).subtype_mk _

/-- Every original point lies in the image of one characteristic closed disk. -/
theorem characteristicQuotient_surjective : Function.Surjective (characteristicQuotient C) := by
  intro x
  have hx : x.val ∈ ⋃ (n : ℕ) (i : RelCWComplex.cell C n), CWComplex.closedCell n i := by
    rw [CWComplex.union]
    exact x.property
  obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨i, z, hz, hzx⟩ := Set.mem_iUnion.mp hx
  exact ⟨⟨n, i, ⟨z, hz⟩⟩, Subtype.ext hzx⟩

variable [T2Space X]

/-- Weak CW topology is precisely the quotient topology of the actual sum of disks. -/
theorem isQuotientMap_characteristicQuotient : IsQuotientMap (characteristicQuotient C) := by
  refine isQuotientMap_iff_isClosed.mpr ⟨characteristicQuotient_surjective C, ?_⟩
  intro S
  constructor
  · exact fun hS => hS.preimage (continuous_characteristicQuotient C)
  · intro hS
    let B : Set X := Subtype.val '' S
    have hB : IsClosed B := by
      apply (CWComplex.closed C B (by rintro _ ⟨x, _, rfl⟩; exact x.property)).mpr
      intro n i
      let P : Set (CharacteristicDisk n) :=
        (fun z => characteristicQuotient C ⟨n, i, z⟩) ⁻¹' S
      have hP : IsClosed P :=
        hS.preimage (continuous_sigmaMk.comp continuous_sigmaMk)
      have hmap : Continuous (fun z : CharacteristicDisk n => RelCWComplex.map n i z) :=
        continuousOn_iff_continuous_domRestrict.mp (RelCWComplex.continuousOn n i)
      have himage : (fun z : CharacteristicDisk n => RelCWComplex.map n i z) '' P =
          B ∩ CWComplex.closedCell n i := by
        ext x
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨⟨characteristicQuotient C ⟨n, i, z⟩, hz, rfl⟩,
            ⟨z, z.property, rfl⟩⟩
        · rintro ⟨⟨y, hy, rfl⟩, z, hz, hzy⟩
          refine ⟨⟨z, hz⟩, ?_, hzy⟩
          change characteristicQuotient C ⟨n, i, ⟨z, hz⟩⟩ ∈ S
          have heq : characteristicQuotient C ⟨n, i, ⟨z, hz⟩⟩ = y := Subtype.ext hzy
          rw [heq]
          exact hy
      rw [← himage]
      exact (hP.isCompact.image hmap).isClosed
    have hpre : Subtype.val ⁻¹' B = S := by
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        have hyx : y = x := Subtype.ext hxy
        exact hyx ▸ hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [← hpre]
    exact hB.preimage continuous_subtype_val

/-- Continuity from the original CW subspace can be tested on its actual disks. -/
theorem continuous_iff_characteristic {Y : Type v} [TopologicalSpace Y] (f : C → Y) :
    Continuous f ↔ ∀ n (i : RelCWComplex.cell C n),
      Continuous (fun z : CharacteristicDisk n => f (characteristicQuotient C ⟨n, i, z⟩)) := by
  rw [(isQuotientMap_characteristicQuotient C).continuous_iff]
  simp only [continuous_sigma_iff, Function.comp_def]

/-- The interval-product continuity descent needed for actual cellwise homotopies. -/
theorem continuous_homotopy_of_characteristic {Y : Type v} [TopologicalSpace Y]
    (H : I × C → Y)
    (hH : Continuous (fun z : I × CharacteristicDomain C =>
      H (z.1, characteristicQuotient C z.2))) : Continuous H :=
  (isQuotientMap_characteristicQuotient C).continuous_lift_prod_right hH

/-- Actual local path connectedness of the classical CW subspace follows by quotient descent. -/
theorem locallyPathConnectedSpace : LocallyPathConnectedSpace C := by
  let (n : ℕ) : LocallyPathConnectedSpace (CharacteristicDisk n) :=
    (convex_closedBall (0 : Fin n → ℝ) 1).locallyPathConnectedSpace
  exact (isQuotientMap_characteristicQuotient C).locallyPathConnectedSpace

end Topology.CWComplex
