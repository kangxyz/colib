/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.SkeletonAttachment

/-!
# Continuous extension across one actual classical-CW skeleton

Only agreement of the prescribed disk maps with the prescribed old-skeleton
map on their literal sphere boundaries is assumed. Fiberwise compatibility is
proved from original open-cell disjointness and characteristic interior
injectivity. The actual step quotient then gives the unique continuous map.

Adapted from `Quillen/Topology/CWComplex/SkeletonExtension.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

open Topology
noncomputable section
open Set Metric
universe u v
namespace Topology.CWComplex
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C] (n : ℕ)
variable {Y : Type v} [TopologicalSpace Y]
variable (a : C(SkeletonLT C n, Y))
variable (b : ∀ _ : RelCWComplex.cell C n, C(CharacteristicDisk n, Y))

/-- The prescribed values on the displayed sum before quotient descent. -/
def skeletonStepData : SkeletonStepDomain C n → Y :=
  Sum.elim a (fun z ↦ b z.1 z.2)

/-- The supplied continuous maps give a continuous map on the displayed sum. -/
theorem continuous_skeletonStepData : Continuous (skeletonStepData C n a b) :=
  continuous_sum_dom.mpr ⟨a.continuous, continuous_sigma (fun i ↦ (b i).continuous)⟩

/-- Boundary agreement controls every disk value whose image lies in the old skeleton. -/
theorem diskValue_eq_old_of_mem
    (hab : ∀ i t, b i (characteristicSphereInclusion n t) =
      a (characteristicBoundaryMap C n i t))
    (i : RelCWComplex.cell C n) (z : CharacteristicDisk n)
    (hz : RelCWComplex.map n i z ∈ (CWComplex.skeletonLT C n : Set X)) :
    b i z = a ⟨RelCWComplex.map n i z, hz⟩ := by
  have hs := (characteristic_mem_previous_iff C n i z).mp hz
  exact hab i ⟨z.val, hs⟩

/-- Equal original characteristic images force equal prescribed values. On the
boundary this follows from the old map; away from it, disjointness identifies
the cell and its actual partial equivalence identifies the disk point. -/
theorem diskValues_eq_of_same_image
    (hab : ∀ i t, b i (characteristicSphereInclusion n t) =
      a (characteristicBoundaryMap C n i t))
    (i j : RelCWComplex.cell C n) (z w : CharacteristicDisk n)
    (he : RelCWComplex.map n i z = RelCWComplex.map n j w) : b i z = b j w := by
  by_cases hz : RelCWComplex.map n i z ∈ (CWComplex.skeletonLT C n : Set X)
  · have hw : RelCWComplex.map n j w ∈ (CWComplex.skeletonLT C n : Set X) := he ▸ hz
    rw [diskValue_eq_old_of_mem C n a b hab i z hz,
      diskValue_eq_old_of_mem C n a b hab j w hw]
    exact congrArg a (Subtype.ext he)
  · have hw : RelCWComplex.map n j w ∉ (CWComplex.skeletonLT C n : Set X) := by
      simpa only [← he] using hz
    have hzb : z.val ∈ ball (0 : Fin n → ℝ) 1 := by
      rw [← closedBall_sdiff_sphere]
      exact ⟨z.property, fun hs ↦ hz ((characteristic_mem_previous_iff C n i z).mpr hs)⟩
    have hwb : w.val ∈ ball (0 : Fin n → ℝ) 1 := by
      rw [← closedBall_sdiff_sphere]
      exact ⟨w.property, fun hs ↦ hw ((characteristic_mem_previous_iff C n j w).mpr hs)⟩
    have hij : i = j := by
      by_contra hne
      have hd := RelCWComplex.disjoint_openCell_of_ne
        (by simpa using hne : (⟨n, i⟩ : Σ m, RelCWComplex.cell C m) ≠ ⟨n, j⟩)
      exact hd.notMem_of_mem_left ⟨z, hzb, rfl⟩ ⟨w, hwb, he.symm⟩
    subst j
    have hzw : z.val = w.val := (RelCWComplex.map n i).injOn
      (by rwa [RelCWComplex.source_eq]) (by rwa [RelCWComplex.source_eq]) he
    exact congrArg (b i) (Subtype.ext hzw)

/-- Compatibility on every fiber is derived from the sphere-boundary agreement.
It is not a premise or a supplied target-bearing attachment certificate. -/
theorem skeletonStepData_fiberwise
    (hab : ∀ i t, b i (characteristicSphereInclusion n t) =
      a (characteristicBoundaryMap C n i t))
    (x y : SkeletonStepDomain C n)
    (h : skeletonStepMap C n x = skeletonStepMap C n y) :
    skeletonStepData C n a b x = skeletonStepData C n a b y := by
  have he := congrArg Subtype.val h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg a (Subtype.ext he)
    | inr y =>
      obtain ⟨i, z⟩ := y
      change x.val = RelCWComplex.map n i z at he
      have hz : RelCWComplex.map n i z ∈ (CWComplex.skeletonLT C n : Set X) := he ▸ x.property
      change a x = b i z
      exact ((diskValue_eq_old_of_mem C n a b hab i z hz).trans
        (congrArg a (Subtype.ext he.symm))).symm
  | inr x =>
    obtain ⟨i, z⟩ := x
    cases y with
    | inl y =>
      change RelCWComplex.map n i z = y.val at he
      have hz : RelCWComplex.map n i z ∈ (CWComplex.skeletonLT C n : Set X) := he.symm ▸ y.property
      change b i z = a y
      exact (diskValue_eq_old_of_mem C n a b hab i z hz).trans
        (congrArg a (Subtype.ext he))
    | inr y =>
      obtain ⟨j, w⟩ := y
      exact diskValues_eq_of_same_image C n a b hab i j z w he

/-- Set-theoretic descent uses a representative of the proved-surjective actual
step map. The next theorem proves independence of that representative. -/
def skeletonStepExtensionFun (y : SkeletonLT C (n + 1)) : Y :=
  skeletonStepData C n a b (Classical.choose (skeletonStepMap_surjective C n y))

/-- Descent recovers the prescribed value on every point of the displayed sum. -/
theorem skeletonStepExtensionFun_map
    (hab : ∀ i t, b i (characteristicSphereInclusion n t) =
      a (characteristicBoundaryMap C n i t)) (x : SkeletonStepDomain C n) :
    skeletonStepExtensionFun C n a b (skeletonStepMap C n x) =
      skeletonStepData C n a b x :=
  skeletonStepData_fiberwise C n a b hab _ x
    (Classical.choose_spec (skeletonStepMap_surjective C n (skeletonStepMap C n x)))

/-- Quotient descent proves continuity on the original next-skeleton subtype. -/
theorem continuous_skeletonStepExtensionFun
    (hab : ∀ i t, b i (characteristicSphereInclusion n t) =
      a (characteristicBoundaryMap C n i t)) :
    Continuous (skeletonStepExtensionFun C n a b) := by
  apply (isQuotientMap_skeletonStepMap C n).continuous_iff.mpr
  have he : skeletonStepExtensionFun C n a b ∘ skeletonStepMap C n =
      skeletonStepData C n a b := funext (skeletonStepExtensionFun_map C n a b hab)
  rw [he]
  exact continuous_skeletonStepData C n a b

/-- Extend the prescribed old-skeleton map and prescribed disk maps continuously
across the actual next skeleton, using only their original boundary agreement. -/
def skeletonStepExtension
    (hab : ∀ i t, b i (characteristicSphereInclusion n t) =
      a (characteristicBoundaryMap C n i t)) : C(SkeletonLT C (n + 1), Y) :=
  ⟨skeletonStepExtensionFun C n a b, continuous_skeletonStepExtensionFun C n a b hab⟩

/-- The old skeleton is retained pointwise. -/
theorem skeletonStepExtension_old
    (hab : ∀ i t, b i (characteristicSphereInclusion n t) =
      a (characteristicBoundaryMap C n i t)) (x : SkeletonLT C n) :
    skeletonStepExtension C n a b hab (skeletonInclusion C n x) = a x :=
  skeletonStepExtensionFun_map C n a b hab (Sum.inl x)

/-- Each original new disk map is retained pointwise, including its boundary. -/
theorem skeletonStepExtension_disk
    (hab : ∀ i t, b i (characteristicSphereInclusion n t) =
      a (characteristicBoundaryMap C n i t)) (i : RelCWComplex.cell C n)
    (z : CharacteristicDisk n) :
    skeletonStepExtension C n a b hab (skeletonCharacteristicMap C n i z) = b i z :=
  skeletonStepExtensionFun_map C n a b hab (Sum.inr ⟨i, z⟩)

/-- The actual step map covers all points, so its prescribed restrictions
uniquely determine the extension as a continuous map. -/
theorem skeletonStepExtension_unique
    (hab : ∀ i t, b i (characteristicSphereInclusion n t) =
      a (characteristicBoundaryMap C n i t))
    (f : C(SkeletonLT C (n + 1), Y))
    (hf_old : ∀ x, f (skeletonInclusion C n x) = a x)
    (hf_disk : ∀ i z, f (skeletonCharacteristicMap C n i z) = b i z) :
    f = skeletonStepExtension C n a b hab := by
  ext y
  obtain ⟨x, rfl⟩ := skeletonStepMap_surjective C n y
  cases x with
  | inl x => exact (hf_old x).trans (skeletonStepExtension_old C n a b hab x).symm
  | inr z =>
    exact (hf_disk z.1 z.2).trans (skeletonStepExtension_disk C n a b hab z.1 z.2).symm

end Topology.CWComplex
