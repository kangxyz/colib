/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.SkeletonExtension
public import Colib.Topology.CWComplex.CubeDiskPair

/-!
# Compatible actual lifts on all finite classical-CW skeleta

Strict cubical boundary lifting supplies each original disk lift. The proved
one-step characteristic quotient glues those lifts and retains the previous
skeleton pointwise. Dimension induction starts with the literal empty skeleton;
no nonempty-space assumption or supplied global lifting certificate is used.

Adapted from `Quillen/Topology/CWComplex/SkeletonLifting.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

open Topology
noncomputable section
open Set
universe u v w
namespace Topology.CWComplex
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]

/-- The unchanged inclusion of a finite skeleton into the original CW subtype. -/
def skeletonToComplex (n : ℕ) : C(SkeletonLT C n, C) :=
  ⟨fun x ↦ ⟨x.val, (CWComplex.skeletonLT C n).subset_complex x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- The actual inclusion of any earlier skeleton into any later one. -/
def skeletonInclusionLE {n m : ℕ} (h : n ≤ m) : C(SkeletonLT C n, SkeletonLT C m) :=
  ⟨fun x ↦ ⟨x.val, CWComplex.skeletonLT_mono (by exact_mod_cast h) x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- The strict original base map does not change when a point is moved to a later skeleton. -/
theorem skeletonToComplex_inclusionLE {n m : ℕ} (h : n ≤ m) (x : SkeletonLT C n) :
    skeletonToComplex C m (skeletonInclusionLE C h x) = skeletonToComplex C n x := rfl

/-- Disk boundary lifting and the genuine step quotient construct an actual
one-step lift with the specified previous-skeleton values. -/
theorem exists_skeletonStepLift (p : C(E, B)) (hp : CubicalSubdivision.BoundaryLifting p)
    (n : ℕ) (a : C(SkeletonLT C n, E)) (d : C(SkeletonLT C (n + 1), B))
    (ha : ∀ x, p (a x) = d (skeletonInclusion C n x)) :
    ∃ c : C(SkeletonLT C (n + 1), E),
      (∀ x, c (skeletonInclusion C n x) = a x) ∧ p.comp c = d := by
  have lifts : ∀ i : RelCWComplex.cell C n,
      ∃ b : C(CharacteristicDisk n, E),
        (∀ z, b (characteristicSphereInclusion n z) = a (characteristicBoundaryMap C n i z)) ∧
          p.comp b = d.comp (skeletonCharacteristicMap C n i) := by
    intro i
    apply hp.characteristicDisk n (a.comp (characteristicBoundaryMap C n i))
      (d.comp (skeletonCharacteristicMap C n i))
    intro z
    change p (a (characteristicBoundaryMap C n i z)) =
      d (skeletonCharacteristicMap C n i (characteristicSphereInclusion n z))
    rw [skeletonCharacteristicMap_boundary]
    exact ha _
  choose b hb_boundary hb_over using lifts
  refine ⟨skeletonStepExtension C n a b hb_boundary,
    skeletonStepExtension_old C n a b hb_boundary, ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := skeletonStepMap_surjective C n y
  cases x with
  | inl x =>
    change p (skeletonStepExtension C n a b hb_boundary (skeletonInclusion C n x)) = _
    rw [skeletonStepExtension_old]
    exact ha x
  | inr z =>
    change p (skeletonStepExtension C n a b hb_boundary
      (skeletonCharacteristicMap C n z.1 z.2)) = _
    rw [skeletonStepExtension_disk]
    exact ContinuousMap.congr_fun (hb_over z.1) z.2

variable (p : C(E, B)) (hp : CubicalSubdivision.BoundaryLifting p) (f : C(C, B))

/-- Internal finite-stage data: an actual continuous map and its strict original
base equation. Such data are constructed by recursion, never a global premise. -/
abbrev SkeletonLiftAt (n : ℕ) :=
  {a : C(SkeletonLT C n, E) // ∀ x, p (a x) = f (skeletonToComplex C n x)}

/-- There is an initial lift because the previous zero skeleton is empty,
including when the total space E itself is empty. -/
def initialSkeletonLift : SkeletonLiftAt C p f 0 := by
  letI := skeletonLT_zero_isEmpty C
  let a : C(SkeletonLT C 0, E) :=
    ⟨fun x ↦ isEmptyElim x, by
      rw [continuous_iff_continuousAt]
      intro x
      exact isEmptyElim x⟩
  exact ⟨a, fun x ↦ isEmptyElim x⟩

/-- A genuinely supplied boundary-lifting map extends every constructed finite
stage; both the old map and the original target map remain literal. -/
def nextSkeletonLift (n : ℕ) (a : SkeletonLiftAt C p f n) :
    SkeletonLiftAt C p f (n + 1) := by
  let h := exists_skeletonStepLift C p hp n a.val
    (f.comp (skeletonToComplex C (n + 1))) (fun x ↦ a.property x)
  exact ⟨Classical.choose h, fun x ↦ ContinuousMap.congr_fun (Classical.choose_spec h).2 x⟩

/-- The chosen next stage has the proved prescribed old-skeleton restriction. -/
theorem nextSkeletonLift_old (n : ℕ) (a : SkeletonLiftAt C p f n)
    (x : SkeletonLT C n) :
    (nextSkeletonLift C p hp f n a).val (skeletonInclusion C n x) = a.val x :=
  (Classical.choose_spec (exists_skeletonStepLift C p hp n a.val
    (f.comp (skeletonToComplex C (n + 1))) (fun x ↦ a.property x))).1 x

/-- Actual compatible lifts are constructed by dimension induction. -/
def skeletonLiftFamily : (n : ℕ) → SkeletonLiftAt C p f n :=
  Nat.rec (initialSkeletonLift C p f) (fun n a ↦ nextSkeletonLift C p hp f n a)

/-- Adjacent stages agree at every actual point of the old skeleton. -/
theorem skeletonLiftFamily_succ (n : ℕ) (x : SkeletonLT C n) :
    (skeletonLiftFamily C p hp f (n + 1)).val (skeletonInclusion C n x) =
      (skeletonLiftFamily C p hp f n).val x :=
  nextSkeletonLift_old C p hp f n (skeletonLiftFamily C p hp f n) x

/-- Every earlier stage agrees with every later stage on original points. -/
theorem skeletonLiftFamily_compatible {n m : ℕ} (h : n ≤ m) (x : SkeletonLT C n) :
    (skeletonLiftFamily C p hp f m).val (skeletonInclusionLE C h x) =
      (skeletonLiftFamily C p hp f n).val x := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m h ih =>
    change (skeletonLiftFamily C p hp f (m + 1)).val
      (skeletonInclusion C m (skeletonInclusionLE C h x)) = _
    rw [skeletonLiftFamily_succ]
    exact ih

end Topology.CWComplex
