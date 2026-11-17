/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# The intrinsic classical CW structure on the actual complex subtype

The original characteristic maps are retained on their entire closed disks.
Their irrelevant values outside those disks are replaced by a supplied point
of the complex. This makes their codomains the actual subtype, and the inverse
maps remain the original inverse maps composed with subtype inclusion.

All CW fields are constructed directly. In particular, closure-finiteness
uses the same finite cell carriers and weak topology is transported through
the actual closed subtype inclusion. No homeomorphism-transport theorem or
conversion to the abstract categorical CW notion is assumed.

Adapted from `Quillen/Topology/CWComplex/Subtype.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

open Topology
noncomputable section
open Set Metric
universe u
namespace Topology.CWComplex
variable {X : Type u} [TopologicalSpace X]
variable (C : Set X) [CWComplex C] (c : C)

/-- The original characteristic function on the closed disk, with an irrelevant
outside value chosen in the actual complex so the codomain is the subtype. -/
def subtypeCharacteristicFun (n : ℕ) (i : RelCWComplex.cell C n) (z : Fin n → ℝ) : C := by
  classical
  exact if hz : z ∈ closedBall (0 : Fin n → ℝ) 1 then
    ⟨RelCWComplex.map n i z, CWComplex.closedCell_subset_complex n i ⟨z, hz, rfl⟩⟩
  else c

/-- Every original closed-disk value is preserved literally. -/
theorem subtypeCharacteristicFun_val (n : ℕ) (i : RelCWComplex.cell C n)
    (z : Fin n → ℝ) (hz : z ∈ closedBall (0 : Fin n → ℝ) 1) :
    (subtypeCharacteristicFun C c n i z).val = RelCWComplex.map n i z := by
  simp only [subtypeCharacteristicFun, dite_eq_left hz]

/-- The intrinsic characteristic partial equivalence has exactly the original
open-ball source and the original target restricted to the actual subtype. -/
def subtypeCharacteristicMap (n : ℕ) (i : RelCWComplex.cell C n) :
    PartialEquiv (Fin n → ℝ) C where
  toFun := subtypeCharacteristicFun C c n i
  invFun x := (RelCWComplex.map n i).symm x.val
  source := ball 0 1
  target := Subtype.val ⁻¹' (RelCWComplex.map n i).target
  map_source' := by
    intro z hz
    change (subtypeCharacteristicFun C c n i z).val ∈ (RelCWComplex.map n i).target
    rw [subtypeCharacteristicFun_val C c n i z (ball_subset_closedBall hz)]
    exact (RelCWComplex.map n i).map_source (by rwa [RelCWComplex.source_eq])
  map_target' := by
    intro x hx
    simpa only [← RelCWComplex.source_eq n i] using (RelCWComplex.map n i).map_target hx
  left_inv' := by
    intro z hz
    rw [subtypeCharacteristicFun_val C c n i z (ball_subset_closedBall hz)]
    exact (RelCWComplex.map n i).left_inv (by rwa [RelCWComplex.source_eq])
  right_inv' := by
    intro x hx
    have hz : (RelCWComplex.map n i).symm x.val ∈ ball (0 : Fin n → ℝ) 1 := by
      simpa only [← RelCWComplex.source_eq n i] using (RelCWComplex.map n i).map_target hx
    apply Subtype.ext
    rw [subtypeCharacteristicFun_val C c n i _ (ball_subset_closedBall hz)]
    exact (RelCWComplex.map n i).right_inv hx

/-- The intrinsic chart retains the original characteristic value on the closed disk. -/
theorem subtypeCharacteristicMap_val (n : ℕ) (i : RelCWComplex.cell C n)
    (z : Fin n → ℝ) (hz : z ∈ closedBall (0 : Fin n → ℝ) 1) :
    (subtypeCharacteristicMap C c n i z).val = RelCWComplex.map n i z :=
  subtypeCharacteristicFun_val C c n i z hz

/-- Images of every subset of the closed disk are the original images in the subtype. -/
theorem subtypeCharacteristicMap_image (n : ℕ) (i : RelCWComplex.cell C n)
    (S : Set (Fin n → ℝ)) (hS : S ⊆ closedBall 0 1) :
    subtypeCharacteristicMap C c n i '' S = Subtype.val ⁻¹' (RelCWComplex.map n i '' S) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (subtypeCharacteristicMap_val C c n i z (hS hz)).symm⟩
  · rintro ⟨z, hz, he⟩
    refine ⟨z, hz, Subtype.ext ?_⟩
    rw [subtypeCharacteristicMap_val C c n i z (hS hz)]
    exact he

/-- Closed-disk continuity is inherited from the original characteristic map. -/
theorem continuousOn_subtypeCharacteristicMap (n : ℕ) (i : RelCWComplex.cell C n) :
    ContinuousOn (subtypeCharacteristicMap C c n i) (closedBall 0 1) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply continuous_induced_rng.mpr
  have he : (Subtype.val ∘ (closedBall (0 : Fin n → ℝ) 1).domRestrict
      (subtypeCharacteristicMap C c n i)) =
      (closedBall (0 : Fin n → ℝ) 1).domRestrict (RelCWComplex.map n i) := by
    funext z
    exact subtypeCharacteristicMap_val C c n i z.val z.property
  rw [he]
  exact (RelCWComplex.continuousOn n i).domRestrict

/-- The intrinsic inverse is still the original inverse after subtype inclusion. -/
theorem continuousOn_subtypeCharacteristicMap_symm (n : ℕ) (i : RelCWComplex.cell C n) :
    ContinuousOn (subtypeCharacteristicMap C c n i).symm
      (subtypeCharacteristicMap C c n i).target :=
  (RelCWComplex.continuousOn_symm n i).comp continuous_subtype_val.continuousOn
    (fun _ hx ↦ hx)

variable [T2Space X]

/-- The actual complex, with its original subtype topology, is a classical CW
complex on its whole underlying type. All characteristic data are constructed. -/
@[instance_reducible]
def subtypeCWComplex : CWComplex (univ : Set C) where
  cell := RelCWComplex.cell C
  map := subtypeCharacteristicMap C c
  source_eq := fun _ _ ↦ rfl
  continuousOn := continuousOn_subtypeCharacteristicMap C c
  continuousOn_symm := continuousOn_subtypeCharacteristicMap_symm C c
  pairwiseDisjoint' := by
    intro a ha b hb hab
    change Disjoint (subtypeCharacteristicMap C c a.1 a.2 '' ball 0 1)
      (subtypeCharacteristicMap C c b.1 b.2 '' ball 0 1)
    rw [subtypeCharacteristicMap_image C c a.1 a.2 _ ball_subset_closedBall,
      subtypeCharacteristicMap_image C c b.1 b.2 _ ball_subset_closedBall]
    exact Disjoint.preimage Subtype.val (CWComplex.disjoint_openCell_of_ne hab)
  mapsTo' := by
    intro n i
    obtain ⟨I, hI⟩ := CWComplex.mapsTo n i
    refine ⟨I, ?_⟩
    intro z hz
    simp_rw [subtypeCharacteristicMap_image C c _ _ _ subset_rfl, ← preimage_iUnion]
    change (subtypeCharacteristicMap C c n i z).val ∈
      ⋃ (m < n) (j ∈ I m), RelCWComplex.map m j '' closedBall 0 1
    rw [subtypeCharacteristicMap_val C c n i z (sphere_subset_closedBall hz)]
    exact hI hz
  closed' := by
    intro A _hA hA
    have hc : IsClosed (Subtype.val '' A : Set X) := by
      apply (CWComplex.closed C _ (by rintro _ ⟨x, _hx, rfl⟩; exact x.property)).mpr
      intro n i
      have h := (CWComplex.isClosed (C := C)).isClosedMap_subtype_val _ (hA n i)
      rw [subtypeCharacteristicMap_image C c n i _ subset_rfl, image_inter_preimage] at h
      exact h
    have he : Subtype.val ⁻¹' (Subtype.val '' A) = A := Subtype.val_injective.preimage_image A
    rw [← he]
    exact hc.preimage continuous_subtype_val
  union' := by
    simp_rw [subtypeCharacteristicMap_image C c _ _ _ subset_rfl, ← preimage_iUnion]
    change Subtype.val ⁻¹' (⋃ n, ⋃ i : RelCWComplex.cell C n, RelCWComplex.closedCell n i) = univ
    rw [CWComplex.union]
    ext x
    simp

end Topology.CWComplex
