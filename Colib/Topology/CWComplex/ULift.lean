/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.Constructions

/-!
# Universe lifting of classical CW structures

`uliftCWComplex` lifts an ambient classical CW complex to `ULift X`, with
`ULift` of the original cell indices. The characteristic partial equivalences
are given literally by composition with `ULift.up` and `ULift.down`; no
homeomorphism-transport theorem is assumed. The finite frontier carriers,
weak topology, and union are transported directly from the original structure.

`uliftUnivCWComplex` supplies the corresponding CW structure on all of
`ULift X`. Both constructions are named, instance-reducible definitions rather
than global instances, so clients explicitly choose the universe lift.

Adapted from `Quillen/Topology/CWComplex/ULift.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

open Topology

noncomputable section

open Set Metric

universe u v w

namespace Topology.CWComplex

/-- Lift the codomain of a partial equivalence by the literal up/down maps. -/
def uliftPartialEquiv {A : Type w} {X : Type u} (e : PartialEquiv A X) :
    PartialEquiv A (ULift.{v} X) where
  toFun x := ULift.up (e x)
  invFun x := e.symm x.down
  source := e.source
  target := ULift.down ⁻¹' e.target
  map_source' := fun _ hx ↦ e.map_source hx
  map_target' := fun _ hx ↦ e.map_target hx
  left_inv' := fun _ hx ↦ e.left_inv hx
  right_inv' := fun _ hx ↦ ULift.down_injective (e.right_inv hx)

@[simp] theorem uliftPartialEquiv_apply {A : Type w} {X : Type u}
    (e : PartialEquiv A X) (x : A) :
    (uliftPartialEquiv e : PartialEquiv A (ULift.{v} X)) x = ULift.up (e x) := rfl

@[simp] theorem uliftPartialEquiv_symm_apply {A : Type w} {X : Type u}
    (e : PartialEquiv A X) (x : ULift.{v} X) :
    (uliftPartialEquiv e).symm x = e.symm x.down := rfl

@[simp] theorem uliftPartialEquiv_source {A : Type w} {X : Type u}
    (e : PartialEquiv A X) :
    (uliftPartialEquiv e : PartialEquiv A (ULift.{v} X)).source = e.source := rfl

@[simp] theorem uliftPartialEquiv_target {A : Type w} {X : Type u}
    (e : PartialEquiv A X) :
    (uliftPartialEquiv e : PartialEquiv A (ULift.{v} X)).target =
      ULift.down ⁻¹' e.target := rfl

/-- Every lifted chart image is the full inverse image under `ULift.down`. -/
theorem uliftPartialEquiv_image {A : Type w} {X : Type u}
    (e : PartialEquiv A X) (s : Set A) :
    (uliftPartialEquiv e : PartialEquiv A (ULift.{v} X)) '' s =
      ULift.down ⁻¹' (e '' s) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, ULift.down_injective h⟩

@[simp] theorem preimage_up_uliftPartialEquiv_image {A : Type w} {X : Type u}
    (e : PartialEquiv A X) (s : Set A) :
    (ULift.up : X → ULift.{v} X) ⁻¹' (uliftPartialEquiv e '' s) = e '' s := by
  rw [uliftPartialEquiv_image]
  rfl

variable {X : Type u} [TopologicalSpace X]

/-- Lift all classical CW data, including the cell indexing universes. -/
@[instance_reducible] def uliftCWComplex (C : Set X) [CWComplex C] :
    CWComplex (ULift.down ⁻¹' C : Set (ULift.{v} X)) where
  cell n := ULift.{v} (RelCWComplex.cell C n)
  map n i := uliftPartialEquiv (RelCWComplex.map n i.down)
  source_eq n i := RelCWComplex.source_eq n i.down
  continuousOn n i :=
    continuous_uliftUp.comp_continuousOn (RelCWComplex.continuousOn n i.down)
  continuousOn_symm n i :=
    (RelCWComplex.continuousOn_symm n i.down).comp continuous_uliftDown.continuousOn
      (fun _ hx ↦ hx)
  pairwiseDisjoint' := by
    intro a _ b _ hab
    have hne : (⟨a.1, a.2.down⟩ : Σ n, RelCWComplex.cell C n) ≠ ⟨b.1, b.2.down⟩ := by
      intro h
      apply hab
      exact congrArg
        (fun p : Σ n, RelCWComplex.cell C n ↦
          (⟨p.1, ULift.up p.2⟩ : Σ n, ULift.{v} (RelCWComplex.cell C n))) h
    change Disjoint (uliftPartialEquiv (RelCWComplex.map a.1 a.2.down) '' ball 0 1)
      (uliftPartialEquiv (RelCWComplex.map b.1 b.2.down) '' ball 0 1)
    rw [uliftPartialEquiv_image, uliftPartialEquiv_image]
    exact Disjoint.preimage ULift.down
      (CWComplex.pairwiseDisjoint' (C := C) (mem_univ _) (mem_univ _) hne)
  mapsTo' := by
    intro n i
    obtain ⟨I, hI⟩ := CWComplex.mapsTo' (C := C) n i.down
    refine ⟨fun m ↦ (I m).map ⟨ULift.up, ULift.up_injective⟩, ?_⟩
    intro x hx
    have hx' := hI hx
    simp only [mem_iUnion] at hx'
    obtain ⟨m, hmn, j, hj, hxj⟩ := hx'
    refine mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hmn,
      mem_iUnion.mpr ⟨ULift.up j, mem_iUnion.mpr ⟨?_, ?_⟩⟩⟩⟩
    · exact Finset.mem_map.mpr ⟨j, hj, rfl⟩
    · rw [uliftPartialEquiv_image]
      exact hxj
  closed' := by
    intro A hAC hA
    apply ULift.isClosed_iff.mpr
    apply CWComplex.closed' (C := C) (ULift.up ⁻¹' A)
    · intro x hx
      exact hAC hx
    · intro n j
      change IsClosed (ULift.up ⁻¹' A ∩ RelCWComplex.map (C := C) n j '' closedBall 0 1)
      have h := (hA n (ULift.up j)).preimage continuous_uliftUp
      simpa only [preimage_inter, preimage_up_uliftPartialEquiv_image] using h
  union' := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hx⟩ := mem_iUnion.mp hx
      obtain ⟨i, hx⟩ := mem_iUnion.mp hx
      rw [uliftPartialEquiv_image] at hx
      change x.down ∈ C
      rw [← CWComplex.union' (C := C)]
      exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨i.down, hx⟩⟩
    · intro hx
      change x.down ∈ C at hx
      rw [← CWComplex.union' (C := C)] at hx
      obtain ⟨n, hx⟩ := mem_iUnion.mp hx
      obtain ⟨i, hx⟩ := mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨ULift.up i, ?_⟩⟩
      rw [uliftPartialEquiv_image]
      exact hx

/-- The lifted characteristic maps agree pointwise with the original maps followed by `up`. -/
@[simp] theorem uliftCWComplex_map_apply (C : Set X) [CWComplex C] (n : ℕ)
    (i : ULift.{v} (RelCWComplex.cell C n)) (z : Fin n → ℝ) :
    (uliftCWComplex.{u, v} C).map n i z = ULift.up (RelCWComplex.map n i.down z) := rfl

/-- The inverse lifted chart is the original inverse chart after `down`. -/
@[simp] theorem uliftCWComplex_map_symm_apply (C : Set X) [CWComplex C] (n : ℕ)
    (i : ULift.{v} (RelCWComplex.cell C n)) (z : ULift.{v} X) :
    ((uliftCWComplex.{u, v} C).map n i).symm z = (RelCWComplex.map n i.down).symm z.down := rfl

/-- A named CW structure on the entire lifted ambient space. -/
@[instance_reducible] def uliftUnivCWComplex [CWComplex (univ : Set X)] :
    CWComplex (univ : Set (ULift.{v} X)) :=
  uliftCWComplex.{u, v} (univ : Set X)

end Topology.CWComplex
