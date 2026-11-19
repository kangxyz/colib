/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.CellNeighborhood
public import Colib.Topology.CWComplex.SkeletonNeighborhoodDeformation
public import Colib.Topology.Homotopy.Waiting

/-!
# Exactly compatible contractions of actual skeletal neighborhoods

Starting with one original open n-cell, `skeletalNeighborhood` repeatedly
applies the actual half-radius collar enlargement. Stage k is open in the
original strict skeleton of dimension n + 1 + k. Its inverse image in every
earlier stage is precisely that earlier neighborhood.

For a prescribed point in the original cell, `skeletalNeighborhoodContraction`
constructs ambient contractions to that same original point. Stage k waits
through the positive time `dyadicWait k`. In the next stage the collars move
only between the new and old waiting times, after which the old contraction
is evaluated at its unchanged time. Consequently all finite-stage contractions
agree literally at every time on their common original points.

No finiteness, local-finiteness, or countability assumption is used. All maps
to the whole complex and all inter-stage maps are actual subtype inclusions.
This module does not construct the global union or descend its homotopy.

Adapted from `Quillen/Topology/CWComplex/SkeletalNeighborhoodContractions.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

open Topology
noncomputable section
open Set
open scoped unitInterval
universe u
namespace Topology.CWComplex
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C] (n : ℕ) (i : RelCWComplex.cell C n)

/-- The actual iterated collar neighborhood, indexed by the number of enlargements. -/
def skeletalNeighborhood : (k : ℕ) → Set (SkeletonLT C (n + 1 + k)) :=
  Nat.rec (cellNeighborhoodSet C n i) (fun k U ↦ stepNeighborhood C (n + 1 + k) U)

/-- Each stage retains the original subspace topology of its strict skeleton. -/
abbrev SkeletalNeighborhood (k : ℕ) := ↥(skeletalNeighborhood C n i k)

@[simp] theorem skeletalNeighborhood_zero :
    skeletalNeighborhood C n i 0 = cellNeighborhoodSet C n i := rfl

@[simp] theorem skeletalNeighborhood_succ (k : ℕ) :
    skeletalNeighborhood C n i (k + 1) =
      stepNeighborhood C (n + 1 + k) (skeletalNeighborhood C n i k) := rfl

/-- Openness is in the actual finite skeleton, not asserted in the whole complex. -/
theorem isOpen_skeletalNeighborhood : ∀ k, IsOpen (skeletalNeighborhood C n i k) :=
  Nat.rec (isOpen_cellNeighborhoodSet C n i)
    (fun k hU ↦ isOpen_stepNeighborhood C (n + 1 + k) hU)

/-- The original skeletal inclusion has exactly the preceding neighborhood as preimage. -/
theorem skeletalNeighborhood_preimage_succ (k : ℕ) :
    (skeletonInclusion C (n + 1 + k)) ⁻¹' skeletalNeighborhood C n i (k + 1) =
      skeletalNeighborhood C n i k := by
  ext y
  exact skeletonInclusion_mem_stepNeighborhood C (n + 1 + k)
    (skeletalNeighborhood C n i k) y

/-- Exact inverse-image compatibility under the literal original skeleton subtype
map. The map is written out so this pure geometry does not import skeleton lifting. -/
theorem skeletalNeighborhood_preimage {k l : ℕ} (h : k ≤ l) :
    (fun y : SkeletonLT C (n + 1 + k) ↦
      (⟨y.val, CWComplex.skeletonLT_mono
        (by exact_mod_cast Nat.add_le_add_left h (n + 1)) y.property⟩ :
          SkeletonLT C (n + 1 + l))) ⁻¹' skeletalNeighborhood C n i l =
      skeletalNeighborhood C n i k := by
  ext y
  induction l, h using Nat.le_induction with
  | base => rfl
  | succ l h ih =>
    change skeletonInclusion C (n + 1 + l)
        ⟨y.val, CWComplex.skeletonLT_mono
          (by exact_mod_cast Nat.add_le_add_left h (n + 1)) y.property⟩ ∈
      stepNeighborhood C (n + 1 + l) (skeletalNeighborhood C n i l) ↔
        y ∈ skeletalNeighborhood C n i k
    rw [skeletonInclusion_mem_stepNeighborhood]
    exact ih

/-- The actual inclusion of any earlier neighborhood into any later one. -/
def skeletalNeighborhoodInclusion {k l : ℕ} (h : k ≤ l) :
    C(SkeletalNeighborhood C n i k, SkeletalNeighborhood C n i l) :=
  ⟨fun y ↦ ⟨⟨y.val.val, CWComplex.skeletonLT_mono
      (by exact_mod_cast Nat.add_le_add_left h (n + 1)) y.val.property⟩,
    (Set.ext_iff.mp (skeletalNeighborhood_preimage C n i h) y.val).mpr y.property⟩,
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩

@[simp] theorem skeletalNeighborhoodInclusion_val {k l : ℕ} (h : k ≤ l)
    (y : SkeletalNeighborhood C n i k) :
    (skeletalNeighborhoodInclusion C n i h y).val.val = y.val.val := rfl

@[simp] theorem skeletalNeighborhoodInclusion_refl (k : ℕ)
    (y : SkeletalNeighborhood C n i k) :
    skeletalNeighborhoodInclusion C n i (le_refl k) y = y := rfl

/-- The one-stage inclusion is exactly the inclusion used by the collar deformation. -/
theorem skeletalNeighborhoodInclusion_succ (k : ℕ) (y : SkeletalNeighborhood C n i k) :
    skeletalNeighborhoodInclusion C n i (Nat.le_succ k) y =
      stepNeighborhoodInclusion C (n + 1 + k) (skeletalNeighborhood C n i k)
        (isOpen_skeletalNeighborhood C n i k) y := rfl

@[simp] theorem skeletalNeighborhoodInclusion_trans {k l m : ℕ}
    (hkl : k ≤ l) (hlm : l ≤ m) (y : SkeletalNeighborhood C n i k) :
    skeletalNeighborhoodInclusion C n i hlm (skeletalNeighborhoodInclusion C n i hkl y) =
      skeletalNeighborhoodInclusion C n i (hkl.trans hlm) y := rfl

/-- Each finite-stage map to the whole complex is the original subtype inclusion. -/
def skeletalNeighborhoodToComplex (k : ℕ) : C(SkeletalNeighborhood C n i k, C) :=
  ⟨fun y ↦ ⟨y.val.val, (CWComplex.skeletonLT C (n + 1 + k : ℕ)).subset_complex y.val.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem skeletalNeighborhoodToComplex_val (k : ℕ)
    (y : SkeletalNeighborhood C n i k) :
    (skeletalNeighborhoodToComplex C n i k y).val = y.val.val := rfl

/-- The actual ambient point does not change with the chosen stage. -/
@[simp] theorem skeletalNeighborhoodToComplex_inclusion {k l : ℕ} (h : k ≤ l)
    (y : SkeletalNeighborhood C n i k) :
    skeletalNeighborhoodToComplex C n i l (skeletalNeighborhoodInclusion C n i h y) =
      skeletalNeighborhoodToComplex C n i k y := rfl

/-- Stage zero uses precisely the already constructed original-cell inclusion. -/
theorem skeletalNeighborhoodToComplex_zero :
    skeletalNeighborhoodToComplex C n i 0 = cellNeighborhoodToComplex C n i := rfl

theorem skeletalNeighborhoodToComplex_injective (k : ℕ) :
    Function.Injective (skeletalNeighborhoodToComplex C n i k) := by
  intro y z h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : C ↦ z.val) h

/-- The prescribed seed point, viewed as the very same original point in every stage. -/
def skeletalNeighborhoodSeedPoint (x : CellNeighborhood C n i) (k : ℕ) :
    SkeletalNeighborhood C n i k :=
  skeletalNeighborhoodInclusion C n i (Nat.zero_le k) x

@[simp] theorem skeletalNeighborhoodSeedPoint_val (x : CellNeighborhood C n i) (k : ℕ) :
    (skeletalNeighborhoodSeedPoint C n i x k).val.val = x.val.val := rfl

@[simp] theorem skeletalNeighborhoodToComplex_seedPoint (x : CellNeighborhood C n i) (k : ℕ) :
    skeletalNeighborhoodToComplex C n i k (skeletalNeighborhoodSeedPoint C n i x k) =
      cellNeighborhoodToComplex C n i x := rfl

/-- The actual finite-stage ambient contractions, with decreasing positive waiting
intervals. Every late branch keeps the old homotopy's original time parameter. -/
def skeletalNeighborhoodContraction (x : CellNeighborhood C n i) :
    (k : ℕ) → WaitingHomotopy (skeletalNeighborhoodToComplex C n i k)
      (ContinuousMap.const (SkeletalNeighborhood C n i k) (cellNeighborhoodToComplex C n i x))
      (dyadicWait k) :=
  Nat.rec
      { toHomotopy := cellNeighborhoodAmbientContraction C n i x
        stationary := fun t y ht ↦ cellNeighborhoodAmbientContraction_stationary C n i x y t
          (by simpa only [dyadicWait_zero] using ht) }
    (fun k H ↦ H.extendContraction
        (stepNeighborhoodInclusion C (n + 1 + k) (skeletalNeighborhood C n i k)
          (isOpen_skeletalNeighborhood C n i k))
        (stepNeighborhoodRetraction C (n + 1 + k) (skeletalNeighborhood C n i k)
          (isOpen_skeletalNeighborhood C n i k))
        (stepNeighborhoodDeformation C (n + 1 + k) (skeletalNeighborhood C n i k)
          (isOpen_skeletalNeighborhood C n i k))
        (skeletalNeighborhoodToComplex C n i (k + 1)) (fun _ ↦ rfl)
        (dyadicWait_pos (k + 1)).le (dyadicWait_succ_lt k) (dyadicWait_le_one k))

/-- The literal two-phase formula, including the radial branch at its terminal seam. -/
theorem skeletalNeighborhoodContraction_succ_apply (x : CellNeighborhood C n i)
    (k : ℕ) (t : I) (y : SkeletalNeighborhood C n i (k + 1)) :
    (skeletalNeighborhoodContraction C n i x (k + 1)).toHomotopy (t, y) =
      if (t : ℝ) ≤ dyadicWait k then
        skeletalNeighborhoodToComplex C n i (k + 1)
          (stepNeighborhoodDeformation C (n + 1 + k) (skeletalNeighborhood C n i k)
            (isOpen_skeletalNeighborhood C n i k)
            (waitingRamp (dyadicWait (k + 1)) (dyadicWait k) t, y))
      else (skeletalNeighborhoodContraction C n i x k).toHomotopy
        (t, stepNeighborhoodRetraction C (n + 1 + k) (skeletalNeighborhood C n i k)
          (isOpen_skeletalNeighborhood C n i k) y) := rfl

/-- Every finite stage is stationary on its specified closed initial time interval. -/
theorem skeletalNeighborhoodContraction_stationary (x : CellNeighborhood C n i)
    (k : ℕ) (t : I) (y : SkeletalNeighborhood C n i k) (ht : (t : ℝ) ≤ dyadicWait k) :
    (skeletalNeighborhoodContraction C n i x k).toHomotopy (t, y) =
      skeletalNeighborhoodToComplex C n i k y :=
  (skeletalNeighborhoodContraction C n i x k).stationary t y ht

/-- The initial endpoint is the literal original subtype inclusion. -/
theorem skeletalNeighborhoodContraction_zero (x : CellNeighborhood C n i)
    (k : ℕ) (y : SkeletalNeighborhood C n i k) :
    (skeletalNeighborhoodContraction C n i x k).toHomotopy (0, y) =
      skeletalNeighborhoodToComplex C n i k y :=
  (skeletalNeighborhoodContraction C n i x k).toHomotopy.apply_zero y

/-- Every terminal endpoint is the prescribed original seed point. -/
theorem skeletalNeighborhoodContraction_one (x : CellNeighborhood C n i)
    (k : ℕ) (y : SkeletalNeighborhood C n i k) :
    (skeletalNeighborhoodContraction C n i x k).toHomotopy (1, y) =
      cellNeighborhoodToComplex C n i x :=
  (skeletalNeighborhoodContraction C n i x k).toHomotopy.apply_one y

/-- One enlargement agrees with the old contraction at literally the same time. -/
theorem skeletalNeighborhoodContraction_succ_restrict (x : CellNeighborhood C n i)
    (k : ℕ) (t : I) (y : SkeletalNeighborhood C n i k) :
    (skeletalNeighborhoodContraction C n i x (k + 1)).toHomotopy
      (t, skeletalNeighborhoodInclusion C n i (Nat.le_succ k) y) =
        (skeletalNeighborhoodContraction C n i x k).toHomotopy (t, y) :=
  (skeletalNeighborhoodContraction C n i x k).extendWaiting_restrict
    (stepNeighborhoodInclusion C (n + 1 + k) (skeletalNeighborhood C n i k)
      (isOpen_skeletalNeighborhood C n i k))
    (stepNeighborhoodRetraction C (n + 1 + k) (skeletalNeighborhood C n i k)
      (isOpen_skeletalNeighborhood C n i k))
    (stepNeighborhoodDeformation C (n + 1 + k) (skeletalNeighborhood C n i k)
      (isOpen_skeletalNeighborhood C n i k))
    (skeletalNeighborhoodToComplex C n i (k + 1)) (fun _ ↦ rfl)
    (dyadicWait_pos (k + 1)).le (dyadicWait_succ_lt k) (dyadicWait_le_one k)
    (stepNeighborhoodRetraction_old C (n + 1 + k) (skeletalNeighborhood C n i k)
      (isOpen_skeletalNeighborhood C n i k))
    (stepNeighborhoodDeformation_fixed C (n + 1 + k) (skeletalNeighborhood C n i k)
      (isOpen_skeletalNeighborhood C n i k)) t y

/-- Every later finite-stage contraction agrees with every earlier one at every
time. This is an equality of actual ambient points, not a further homotopy. -/
theorem skeletalNeighborhoodContraction_restrict (x : CellNeighborhood C n i)
    {k l : ℕ} (h : k ≤ l) (t : I) (y : SkeletalNeighborhood C n i k) :
    (skeletalNeighborhoodContraction C n i x l).toHomotopy
      (t, skeletalNeighborhoodInclusion C n i h y) =
        (skeletalNeighborhoodContraction C n i x k).toHomotopy (t, y) := by
  induction l, h using Nat.le_induction with
  | base => rfl
  | succ l h ih =>
    change (skeletalNeighborhoodContraction C n i x (l + 1)).toHomotopy
      (t, skeletalNeighborhoodInclusion C n i (Nat.le_succ l)
        (skeletalNeighborhoodInclusion C n i h y)) = _
    rw [skeletalNeighborhoodContraction_succ_restrict]
    exact ih

/-- Two stage representatives of the same original point give the same value of
the ambient contraction at every time. This is the stage-independence needed
by the eventual whole-complex quotient descent. -/
theorem skeletalNeighborhoodContraction_eq_of_toComplex_eq (x : CellNeighborhood C n i)
    {k l : ℕ} (y : SkeletalNeighborhood C n i k) (z : SkeletalNeighborhood C n i l)
    (h : skeletalNeighborhoodToComplex C n i k y = skeletalNeighborhoodToComplex C n i l z)
    (t : I) :
    (skeletalNeighborhoodContraction C n i x k).toHomotopy (t, y) =
      (skeletalNeighborhoodContraction C n i x l).toHomotopy (t, z) := by
  have he : skeletalNeighborhoodInclusion C n i (Nat.le_max_left k l) y =
      skeletalNeighborhoodInclusion C n i (Nat.le_max_right k l) z := by
    apply skeletalNeighborhoodToComplex_injective C n i (max k l)
    simpa only [skeletalNeighborhoodToComplex_inclusion] using h
  calc
    (skeletalNeighborhoodContraction C n i x k).toHomotopy (t, y) =
        (skeletalNeighborhoodContraction C n i x (max k l)).toHomotopy
          (t, skeletalNeighborhoodInclusion C n i (Nat.le_max_left k l) y) :=
      (skeletalNeighborhoodContraction_restrict C n i x (Nat.le_max_left k l) t y).symm
    _ = (skeletalNeighborhoodContraction C n i x (max k l)).toHomotopy
          (t, skeletalNeighborhoodInclusion C n i (Nat.le_max_right k l) z) := by rw [he]
    _ = (skeletalNeighborhoodContraction C n i x l).toHomotopy (t, z) :=
      skeletalNeighborhoodContraction_restrict C n i x (Nat.le_max_right k l) t z

end Topology.CWComplex
