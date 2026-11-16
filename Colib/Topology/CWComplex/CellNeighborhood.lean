/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.SkeletonAttachment
public import Mathlib.Topology.Homotopy.Basic

/-!
# The whole-open-cell seed for a classical CW neighborhood

Each original open n-cell is an open subset of the actual (n + 1)-st strict
skeleton. Its chart is constructed from the original characteristic partial
equivalence and its continuous inverse. Convexity of the literal sup-norm
open disk supplies a contraction to any prescribed point, stationary through
time one half. Zero-dimensional cells are included.

Only one neighborhood at each point is needed by the ambient-thin construction.
Consequently the whole open cell is sufficient; no small-radius refinement or
local-finiteness hypothesis is introduced.

Adapted from `Quillen/Topology/CWComplex/CellNeighborhood.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

open Topology
noncomputable section
open Set Metric
open scoped unitInterval
universe u
namespace Topology.CWComplex

/-- The literal interior of the original characteristic disk. -/
abbrev CharacteristicOpenDisk (n : ℕ) := ↥(ball (0 : Fin n → ℝ) 1)

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C] (n : ℕ) (i : RelCWComplex.cell C n)

/-- The original open cell, viewed inside its first containing strict skeleton. -/
def cellNeighborhoodSet : Set (SkeletonLT C (n + 1)) :=
  {x | x.val ∈ RelCWComplex.openCell n i}

/-- The seed retains the actual subspace topology of the original skeleton. -/
abbrev CellNeighborhood := ↥(cellNeighborhoodSet C n i)

omit [T2Space X] in
theorem openCell_eq_characteristicTarget :
    RelCWComplex.openCell n i = (RelCWComplex.map n i).target := by
  rw [RelCWComplex.openCell, ← RelCWComplex.source_eq (C := C) n i,
    PartialEquiv.image_source_eq_target]

/-- The actual partial equivalence, restricted to its original open disk. -/
def cellNeighborhoodHomeomorph : CharacteristicOpenDisk n ≃ₜ CellNeighborhood C n i where
  toFun z := ⟨⟨RelCWComplex.map n i z,
    CWComplex.closedCell_subset_skeletonLT n i ⟨z, ball_subset_closedBall z.property, rfl⟩⟩,
    ⟨z, z.property, rfl⟩⟩
  invFun x := ⟨(RelCWComplex.map n i).symm x.val.val, by
    rw [← RelCWComplex.source_eq (C := C) n i]
    apply (RelCWComplex.map n i).map_target
    rw [← openCell_eq_characteristicTarget]
    exact x.property⟩
  left_inv z := by
    apply Subtype.ext
    exact (RelCWComplex.map n i).left_inv (by
      simpa only [RelCWComplex.source_eq] using z.property)
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply (RelCWComplex.map n i).right_inv
    rw [← openCell_eq_characteristicTarget]
    exact x.property
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuousOn_iff_continuous_domRestrict.mp
      ((RelCWComplex.continuousOn n i).mono ball_subset_closedBall)
  continuous_invFun := by
    apply Continuous.subtype_mk
    let f : CellNeighborhood C n i → (RelCWComplex.map n i).target := fun x ↦
      ⟨x.val.val, by rw [← openCell_eq_characteristicTarget]; exact x.property⟩
    have hf : Continuous f :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact (continuousOn_iff_continuous_domRestrict.mp
      (RelCWComplex.continuousOn_symm n i)).comp hf

/-- A new characteristic disk meets the selected open cell only in its own
interior, with its own cell index. -/
theorem characteristic_mem_openCell_iff (j : RelCWComplex.cell C n)
    (z : CharacteristicDisk n) :
    RelCWComplex.map n j z ∈ RelCWComplex.openCell n i ↔
      j = i ∧ z.val ∈ ball (0 : Fin n → ℝ) 1 := by
  constructor
  · intro hz
    have hb : z.val ∈ ball (0 : Fin n → ℝ) 1 := by
      rw [← closedBall_sdiff_sphere]
      refine ⟨z.property, fun hs ↦ ?_⟩
      exact (CWComplex.disjoint_skeletonLT_openCell (C := C) (j := i) le_rfl).notMem_of_mem_left
        ((characteristic_mem_previous_iff C n j z).mpr hs) hz
    refine ⟨?_, hb⟩
    by_contra hji
    have hd := RelCWComplex.disjoint_openCell_of_ne
      (by simpa using hji : (⟨n, j⟩ : Σ m, RelCWComplex.cell C m) ≠ ⟨n, i⟩)
    exact hd.notMem_of_mem_left ⟨z, hb, rfl⟩ hz
  · rintro ⟨rfl, hz⟩
    exact ⟨z, hz, rfl⟩

/-- The seed has no point in the previous skeleton. -/
theorem skeletonInclusion_not_mem_cellNeighborhood (x : SkeletonLT C n) :
    skeletonInclusion C n x ∉ cellNeighborhoodSet C n i :=
  (CWComplex.disjoint_skeletonLT_openCell (C := C) (j := i) le_rfl).notMem_of_mem_left x.property

/-- Openness follows from the original one-step quotient, without assuming
that the original open cell is open in the entire complex. -/
theorem isOpen_cellNeighborhoodSet : IsOpen (cellNeighborhoodSet C n i) := by
  apply (isQuotientMap_skeletonStepMap C n).isCoinducing.isOpen_preimage.mp
  apply isOpen_sum_iff.mpr
  constructor
  · have he : Sum.inl ⁻¹' ((skeletonStepMap C n) ⁻¹' cellNeighborhoodSet C n i) = ∅ := by
      ext x
      exact iff_false_intro (skeletonInclusion_not_mem_cellNeighborhood C n i x)
    rw [he]
    exact isOpen_empty
  · apply isOpen_sigma_iff.mpr
    intro j
    by_cases hji : j = i
    · subst j
      have he : Sigma.mk i ⁻¹' (Sum.inr ⁻¹'
          ((skeletonStepMap C n) ⁻¹' cellNeighborhoodSet C n i)) =
          Subtype.val ⁻¹' ball (0 : Fin n → ℝ) 1 := by
        ext z
        exact (characteristic_mem_openCell_iff C n i i z).trans (and_iff_right rfl)
      rw [he]
      exact isOpen_ball.preimage continuous_subtype_val
    · have he : Sigma.mk j ⁻¹' (Sum.inr ⁻¹'
          ((skeletonStepMap C n) ⁻¹' cellNeighborhoodSet C n i)) = ∅ := by
        ext z
        change RelCWComplex.map n j z ∈ RelCWComplex.openCell n i ↔ False
        rw [characteristic_mem_openCell_iff]
        simp only [hji, false_and]
      rw [he]
      exact isOpen_empty

/-- The affine contraction waits through time one half. -/
def cellContractionTime : C(I, I) where
  toFun t := Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)
  continuous_toFun := continuous_projIcc.comp
    ((continuous_const.mul continuous_subtype_val).sub continuous_const)

theorem cellContractionTime_eq_zero (t : I) (ht : (t : ℝ) ≤ 1 / 2) :
    cellContractionTime t = 0 :=
  Set.projIcc_of_le_left zero_le_one (by linarith)

@[simp] theorem cellContractionTime_zero : cellContractionTime 0 = 0 :=
  cellContractionTime_eq_zero 0 (by norm_num)

@[simp] theorem cellContractionTime_one : cellContractionTime 1 = 1 :=
  Set.projIcc_of_right_le zero_le_one (by norm_num)

/-- The convex affine contraction in the unchanged original coordinate ball. -/
def openDiskContraction (z₀ : CharacteristicOpenDisk n) :
    (ContinuousMap.id (CharacteristicOpenDisk n)).Homotopy
      (ContinuousMap.const (CharacteristicOpenDisk n) z₀) where
  toFun p := ⟨(1 - (cellContractionTime p.1 : ℝ)) • p.2.val +
      (cellContractionTime p.1 : ℝ) • z₀.val,
    (convex_ball (0 : Fin n → ℝ) 1) p.2.property z₀.property
      (sub_nonneg.mpr (cellContractionTime p.1).property.2)
      (cellContractionTime p.1).property.1 (sub_add_cancel _ _)⟩
  continuous_toFun := by fun_prop
  map_zero_left z := by apply Subtype.ext; simp
  map_one_left z := by apply Subtype.ext; simp

theorem openDiskContraction_stationary (z₀ z : CharacteristicOpenDisk n)
    (t : I) (ht : (t : ℝ) ≤ 1 / 2) : openDiskContraction n z₀ (t, z) = z := by
  apply Subtype.ext
  change (1 - (cellContractionTime t : ℝ)) • z.val +
    (cellContractionTime t : ℝ) • z₀.val = z.val
  rw [cellContractionTime_eq_zero t ht]
  simp

/-- A prescribed original cell point is the exact final value of its seed contraction. -/
def cellNeighborhoodContraction (x : CellNeighborhood C n i) :
    (ContinuousMap.id (CellNeighborhood C n i)).Homotopy
      (ContinuousMap.const (CellNeighborhood C n i) x) where
  toFun p := cellNeighborhoodHomeomorph C n i
    (openDiskContraction n ((cellNeighborhoodHomeomorph C n i).symm x)
      (p.1, (cellNeighborhoodHomeomorph C n i).symm p.2))
  continuous_toFun := (cellNeighborhoodHomeomorph C n i).continuous.comp
    ((openDiskContraction n ((cellNeighborhoodHomeomorph C n i).symm x)).continuous_toFun.comp
      (continuous_fst.prodMk
        ((cellNeighborhoodHomeomorph C n i).symm.continuous.comp continuous_snd)))
  map_zero_left y := by
    rw [ContinuousMap.Homotopy.apply_zero]
    exact (cellNeighborhoodHomeomorph C n i).apply_symm_apply y
  map_one_left y := by
    rw [ContinuousMap.Homotopy.apply_one]
    exact (cellNeighborhoodHomeomorph C n i).apply_symm_apply x

theorem cellNeighborhoodContraction_stationary (x y : CellNeighborhood C n i)
    (t : I) (ht : (t : ℝ) ≤ 1 / 2) : cellNeighborhoodContraction C n i x (t, y) = y := by
  change cellNeighborhoodHomeomorph C n i
    (openDiskContraction n ((cellNeighborhoodHomeomorph C n i).symm x)
      (t, (cellNeighborhoodHomeomorph C n i).symm y)) = y
  rw [openDiskContraction_stationary n _ _ t ht, Homeomorph.apply_symm_apply]

/-- The seed's inclusion into the actual whole CW subtype. -/
def cellNeighborhoodToComplex : C(CellNeighborhood C n i, C) :=
  ⟨fun x ↦ ⟨x.val.val, RelCWComplex.openCell_subset_complex n i x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

/-- The same actual seed contraction, with values in the original CW subtype. -/
def cellNeighborhoodAmbientContraction (x : CellNeighborhood C n i) :
    (cellNeighborhoodToComplex C n i).Homotopy
      (ContinuousMap.const (CellNeighborhood C n i) (cellNeighborhoodToComplex C n i x)) :=
  ((ContinuousMap.Homotopy.refl (cellNeighborhoodToComplex C n i)).comp
    (cellNeighborhoodContraction C n i x)).cast (by ext; rfl) (by ext; rfl)

theorem cellNeighborhoodAmbientContraction_stationary (x y : CellNeighborhood C n i)
    (t : I) (ht : (t : ℝ) ≤ 1 / 2) :
    cellNeighborhoodAmbientContraction C n i x (t, y) = cellNeighborhoodToComplex C n i y :=
  congrArg (cellNeighborhoodToComplex C n i)
    (cellNeighborhoodContraction_stationary C n i x y t ht)

/-- Every original point belongs to one of the constructed seed neighborhoods. -/
theorem exists_cellNeighborhood (x : C) :
    ∃ (n : ℕ) (i : RelCWComplex.cell C n) (y : CellNeighborhood C n i), y.val.val = x.val := by
  have hx : x.val ∈ ⋃ n, ⋃ i : RelCWComplex.cell C n, RelCWComplex.openCell n i := by
    simpa only [CWComplex.iUnion_openCell_eq_complex] using x.property
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hn
  have hs : x.val ∈ (CWComplex.skeletonLT C (n + 1) : Set X) :=
    CWComplex.closedCell_subset_skeletonLT n i (RelCWComplex.openCell_subset_closedCell n i hi)
  exact ⟨n, i, ⟨⟨x.val, hs⟩, hi⟩, rfl⟩

end Topology.CWComplex
