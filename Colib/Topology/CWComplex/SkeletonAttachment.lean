/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.CharacteristicQuotient
public import Colib.Topology.CWComplex.CharacteristicPair
public import Mathlib.Topology.CWComplex.Classical.Subcomplex

/-!
# The actual one-step characteristic quotient of a classical CW complex

The old skeleton and the original next-dimensional closed disks map onto the
next skeleton. The quotient assertion is derived from the inherited classical
CW structure and its genuine characteristic quotient, not assumed as attachment
data. Both boundary and characteristic maps use the original characteristic
coordinates. The zero-dimensional case is included.

Adapted from `Quillen/Topology/CWComplex/SkeletonAttachment.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

open Topology
noncomputable section
open Set Metric
universe u
namespace Topology.CWComplex
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]

/-- The actual subtype of points in the skeleton of dimensions strictly below n. -/
abbrev SkeletonLT (n : ℕ) := ↥(CWComplex.skeletonLT C n : Set X)

/-- The original inclusion of one skeleton into the next. -/
def skeletonInclusion (n : ℕ) : C(SkeletonLT C n, SkeletonLT C (n + 1)) :=
  ⟨fun x ↦ ⟨x.val, CWComplex.skeletonLT_mono (by exact_mod_cast Nat.le_succ n) x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- A lower-dimensional original characteristic disk lands in the specified skeleton. -/
def characteristicToSkeleton {m n : ℕ} (i : RelCWComplex.cell C m) (h : m < n) :
    C(CharacteristicDisk m, SkeletonLT C n) :=
  ⟨fun z ↦ ⟨RelCWComplex.map m i z,
      CWComplex.skeletonLT_mono (by exact_mod_cast Nat.succ_le_iff.mpr h)
        (CWComplex.closedCell_subset_skeletonLT m i ⟨z, z.property, rfl⟩)⟩,
    (continuousOn_iff_continuous_domRestrict.mp (RelCWComplex.continuousOn m i)).subtype_mk _⟩

/-- The original n-dimensional characteristic map into the next skeleton. -/
def skeletonCharacteristicMap (n : ℕ) (i : RelCWComplex.cell C n) :
    C(CharacteristicDisk n, SkeletonLT C (n + 1)) :=
  characteristicToSkeleton C i (Nat.lt_succ_self n)

/-- The actual sphere boundary map into the previous skeleton. -/
def characteristicBoundaryMap (n : ℕ) (i : RelCWComplex.cell C n) :
    C(CharacteristicSphere n, SkeletonLT C n) :=
  ⟨fun z ↦ ⟨RelCWComplex.map n i z,
      CWComplex.cellFrontier_subset_skeletonLT n i ⟨z, z.property, rfl⟩⟩,
    ((continuousOn_iff_continuous_domRestrict.mp (RelCWComplex.continuousOn n i)).comp
      (characteristicSphereInclusion n).continuous).subtype_mk _⟩

/-- The boundary square commutes pointwise in the original coordinates. -/
theorem skeletonCharacteristicMap_boundary (n : ℕ) (i : RelCWComplex.cell C n)
    (z : CharacteristicSphere n) :
    skeletonCharacteristicMap C n i (characteristicSphereInclusion n z) =
      skeletonInclusion C n (characteristicBoundaryMap C n i z) := rfl

/-- The displayed source consists of the previous skeleton and the original new disks. -/
abbrev SkeletonStepDomain (n : ℕ) :=
  SkeletonLT C n ⊕ (Σ _ : RelCWComplex.cell C n, CharacteristicDisk n)

/-- The actual displayed one-step attachment map. -/
def skeletonStepMap (n : ℕ) : SkeletonStepDomain C n → SkeletonLT C (n + 1) :=
  Sum.elim (skeletonInclusion C n) (fun z ↦ skeletonCharacteristicMap C n z.1 z.2)

/-- Continuity on the previous skeleton and on every actual new disk. -/
theorem continuous_skeletonStepMap (n : ℕ) : Continuous (skeletonStepMap C n) := by
  apply continuous_sum_dom.mpr
  exact ⟨(skeletonInclusion C n).continuous,
    continuous_sigma (fun i ↦ (skeletonCharacteristicMap C n i).continuous)⟩

/-- The genuine set-theoretic skeleton union supplies all points of the next stage. -/
theorem skeletonStepMap_surjective (n : ℕ) : Function.Surjective (skeletonStepMap C n) := by
  intro x
  have hx := x.property
  simp only [Nat.cast_add, Nat.cast_one] at hx
  rw [← CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ n] at hx
  rcases hx with hx | hx
  · exact ⟨Sum.inl ⟨x.val, hx⟩, rfl⟩
  · obtain ⟨i, z, hz, he⟩ := Set.mem_iUnion.mp hx
    exact ⟨Sum.inr ⟨i, ⟨z, hz⟩⟩, Subtype.ext he⟩

/-- An inherited cell of the next skeleton has dimension at most n. -/
theorem skeletonCell_le (n m : ℕ)
    (i : RelCWComplex.cell (CWComplex.skeletonLT C (n + 1) : Set X) m) : m ≤ n := by
  have hi := i.property
  have hm : (m : ℕ∞) < (n + 1 : ℕ) := by
    simpa only [RelCWComplex.skeletonLT, RelCWComplex.Subcomplex.mk',
      Set.mem_ofPred_eq, Nat.cast_add, Nat.cast_one] using hi
  have hm' : m < n + 1 := by exact_mod_cast hm
  exact Nat.lt_succ_iff.mp hm'

/-- Factor each inherited characteristic disk through either the old skeleton
or its literal new disk summand. No choice of cell representative is made. -/
def skeletonCharacteristicFactor (n : ℕ) :
    CharacteristicDomain (CWComplex.skeletonLT C (n + 1) : Set X) →
      SkeletonStepDomain C n := fun ⟨m, i, z⟩ ↦
  if h : m = n then by
    subst m
    exact Sum.inr ⟨i.val, z⟩
  else Sum.inl (characteristicToSkeleton C i.val
    (lt_of_le_of_ne (skeletonCell_le C n m i) h) z)

/-- The factorization is continuous on every inherited disk. -/
theorem continuous_skeletonCharacteristicFactor (n : ℕ) :
    Continuous (skeletonCharacteristicFactor C n) := by
  apply continuous_sigma
  intro m
  apply continuous_sigma
  intro i
  by_cases h : m = n
  · subst m
    have hc : Continuous (fun z : CharacteristicDisk n ↦
        (Sum.inr ⟨i.val, z⟩ : SkeletonStepDomain C n)) :=
      continuous_inr.comp (continuous_sigmaMk (i := i.val))
    simpa only [skeletonCharacteristicFactor, dite_true] using hc
  · have hc : Continuous (fun z : CharacteristicDisk m ↦
        (Sum.inl (characteristicToSkeleton C i.val
          (lt_of_le_of_ne (skeletonCell_le C n m i) h) z) : SkeletonStepDomain C n)) :=
      continuous_inl.comp (characteristicToSkeleton C i.val
        (lt_of_le_of_ne (skeletonCell_le C n m i) h)).continuous
    simpa only [skeletonCharacteristicFactor, dite_eq_right h] using hc

/-- Inherited maps are definitionally the original characteristic maps. -/
theorem skeletonStepMap_comp_characteristicFactor (n : ℕ) :
    skeletonStepMap C n ∘ skeletonCharacteristicFactor C n =
      characteristicQuotient (CWComplex.skeletonLT C (n + 1) : Set X) := by
  funext ⟨m, i, z⟩
  by_cases h : m = n
  · subst m
    simp only [Function.comp_apply, skeletonCharacteristicFactor]
    rfl
  · simp only [Function.comp_apply, skeletonCharacteristicFactor, dite_eq_right h]
    rfl

/-- The displayed step is a genuine quotient, derived from the characteristic
quotient of the inherited next-skeleton CW structure. -/
theorem isQuotientMap_skeletonStepMap (n : ℕ) : IsQuotientMap (skeletonStepMap C n) := by
  apply IsQuotientMap.of_comp (continuous_skeletonCharacteristicFactor C n)
    (continuous_skeletonStepMap C n)
  rw [skeletonStepMap_comp_characteristicFactor]
  exact isQuotientMap_characteristicQuotient (CWComplex.skeletonLT C (n + 1) : Set X)

/-- The initial previous skeleton is genuinely empty. -/
theorem skeletonLT_zero_isEmpty : IsEmpty (SkeletonLT C 0) := by
  constructor
  intro x
  have hx := x.property
  simp only [Nat.cast_zero, CWComplex.skeletonLT_zero_eq_empty, Set.mem_empty_iff_false] at hx

/-- A disk point maps to the old skeleton exactly when it lies on the sphere.
The reverse implication uses genuine disjointness of the open cell and old skeleton. -/
theorem characteristic_mem_previous_iff (n : ℕ) (i : RelCWComplex.cell C n)
    (z : CharacteristicDisk n) :
    RelCWComplex.map n i z ∈ (CWComplex.skeletonLT C n : Set X) ↔
      z.val ∈ sphere (0 : Fin n → ℝ) 1 := by
  constructor
  · intro hz
    by_contra hs
    have hb : z.val ∈ ball (0 : Fin n → ℝ) 1 := by
      rw [← closedBall_sdiff_sphere]
      exact ⟨z.property, hs⟩
    exact (CWComplex.disjoint_skeletonLT_openCell (C := C) (j := i) le_rfl).notMem_of_mem_left
      hz ⟨z, hb, rfl⟩
  · intro hz
    exact CWComplex.cellFrontier_subset_skeletonLT n i ⟨z, hz, rfl⟩

end Topology.CWComplex
