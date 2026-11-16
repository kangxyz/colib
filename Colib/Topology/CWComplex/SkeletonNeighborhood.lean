/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.RadialCollar
public import Colib.Topology.CWComplex.SkeletonAttachment

/-!
# Open neighborhoods across one actual CW skeleton

An open subset of the previous skeleton is enlarged by the radial collar over
its inverse image on each original attaching sphere. The resulting subset of
the next skeleton is open, and its inverse image in the old skeleton is exactly
the starting subset. These assertions follow from the actual attachment
quotient, with saturation proved using characteristic interior injectivity and
open-cell disjointness.

The quotient restricted to this open neighborhood is explicitly retained. In
particular, none of these open subsets is assumed to have a CW structure.

Adapted from `Quillen/Topology/CWComplex/SkeletonNeighborhood.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

open Topology
noncomputable section
open Set Metric
universe u
namespace Topology.CWComplex
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C] (n : ℕ)

/-- Directions whose original attaching value belongs to the previous neighborhood. -/
def stepCollarDirections (U : Set (SkeletonLT C n)) (i : RelCWComplex.cell C n) :
    Set (CharacteristicSphere n) := (characteristicBoundaryMap C n i) ⁻¹' U

/-- The old open set and all its literal disk collars in the displayed attachment source. -/
def stepNeighborhoodSource (U : Set (SkeletonLT C n)) : Set (SkeletonStepDomain C n) :=
  {z | Sum.elim (fun x ↦ x ∈ U)
    (fun w ↦ w.2 ∈ radialCollarSet n (stepCollarDirections C n U w.1)) z}

/-- The actual next-skeleton subset obtained by attaching these collars. -/
def stepNeighborhood (U : Set (SkeletonLT C n)) : Set (SkeletonLT C (n + 1)) :=
  skeletonStepMap C n '' stepNeighborhoodSource C n U

theorem disk_mem_stepNeighborhoodSource_of_previous (U : Set (SkeletonLT C n))
    (i : RelCWComplex.cell C n) (z : CharacteristicDisk n)
    (hz : RelCWComplex.map n i z ∈ (CWComplex.skeletonLT C n : Set X)) :
    Sum.inr ⟨i, z⟩ ∈ stepNeighborhoodSource C n U ↔
      (⟨RelCWComplex.map n i z, hz⟩ : SkeletonLT C n) ∈ U := by
  let w : CharacteristicSphere n :=
    ⟨z.val, (characteristic_mem_previous_iff C n i z).mp hz⟩
  change characteristicSphereInclusion n w ∈
    radialCollarSet n (stepCollarDirections C n U i) ↔ _
  rw [sphere_mem_radialCollarSet]
  rfl

/-- Equal original new-disk images are indistinguishable by collar membership. -/
theorem disk_stepNeighborhoodSource_iff_of_same_image (U : Set (SkeletonLT C n))
    (i j : RelCWComplex.cell C n) (z w : CharacteristicDisk n)
    (he : RelCWComplex.map n i z = RelCWComplex.map n j w) :
    Sum.inr ⟨i, z⟩ ∈ stepNeighborhoodSource C n U ↔
      Sum.inr ⟨j, w⟩ ∈ stepNeighborhoodSource C n U := by
  by_cases hz : RelCWComplex.map n i z ∈ (CWComplex.skeletonLT C n : Set X)
  · have hw : RelCWComplex.map n j w ∈ (CWComplex.skeletonLT C n : Set X) := he ▸ hz
    rw [disk_mem_stepNeighborhoodSource_of_previous C n U i z hz,
      disk_mem_stepNeighborhoodSource_of_previous C n U j w hw]
    exact iff_of_eq (congrArg (fun x : SkeletonLT C n ↦ x ∈ U) (Subtype.ext he))
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
    have hzw : z = w := Subtype.ext ((RelCWComplex.map n i).injOn
      (by rwa [RelCWComplex.source_eq]) (by rwa [RelCWComplex.source_eq]) he)
    subst w
    rfl

/-- Saturation is a geometric consequence, not a property supplied by the caller. -/
theorem stepNeighborhoodSource_fiberwise (U : Set (SkeletonLT C n))
    (x y : SkeletonStepDomain C n) (h : skeletonStepMap C n x = skeletonStepMap C n y) :
    x ∈ stepNeighborhoodSource C n U ↔ y ∈ stepNeighborhoodSource C n U := by
  have he := congrArg Subtype.val h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      exact iff_of_eq (congrArg (fun z : SkeletonLT C n ↦ z ∈ U) (Subtype.ext he))
    | inr y =>
      obtain ⟨i, z⟩ := y
      change x.val = RelCWComplex.map n i z at he
      have hz : RelCWComplex.map n i z ∈ (CWComplex.skeletonLT C n : Set X) := he ▸ x.property
      rw [disk_mem_stepNeighborhoodSource_of_previous C n U i z hz]
      exact iff_of_eq (congrArg (fun z : SkeletonLT C n ↦ z ∈ U) (Subtype.ext he))
  | inr x =>
    obtain ⟨i, z⟩ := x
    cases y with
    | inl y =>
      change RelCWComplex.map n i z = y.val at he
      have hz : RelCWComplex.map n i z ∈ (CWComplex.skeletonLT C n : Set X) := he.symm ▸ y.property
      rw [disk_mem_stepNeighborhoodSource_of_previous C n U i z hz]
      exact iff_of_eq (congrArg (fun z : SkeletonLT C n ↦ z ∈ U) (Subtype.ext he))
    | inr y =>
      obtain ⟨j, w⟩ := y
      exact disk_stepNeighborhoodSource_iff_of_same_image C n U i j z w he

theorem preimage_stepNeighborhood (U : Set (SkeletonLT C n)) :
    (skeletonStepMap C n) ⁻¹' stepNeighborhood C n U = stepNeighborhoodSource C n U := by
  ext z
  constructor
  · rintro ⟨w, hw, he⟩
    exact (stepNeighborhoodSource_fiberwise C n U w z he).mp hw
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- Every old point belongs to the enlarged neighborhood exactly when it belonged before. -/
theorem skeletonInclusion_mem_stepNeighborhood (U : Set (SkeletonLT C n))
    (x : SkeletonLT C n) : skeletonInclusion C n x ∈ stepNeighborhood C n U ↔ x ∈ U := by
  have h := Set.ext_iff.mp (preimage_stepNeighborhood C n U) (Sum.inl x)
  exact h

/-- Every new-disk inverse image is exactly its prescribed literal collar. -/
theorem skeletonCharacteristicMap_mem_stepNeighborhood (U : Set (SkeletonLT C n))
    (i : RelCWComplex.cell C n) (z : CharacteristicDisk n) :
    skeletonCharacteristicMap C n i z ∈ stepNeighborhood C n U ↔
      z ∈ radialCollarSet n (stepCollarDirections C n U i) := by
  exact Set.ext_iff.mp (preimage_stepNeighborhood C n U) (Sum.inr ⟨i, z⟩)

theorem isOpen_stepNeighborhoodSource {U : Set (SkeletonLT C n)} (hU : IsOpen U) :
    IsOpen (stepNeighborhoodSource C n U) := by
  apply isOpen_sum_iff.mpr
  refine ⟨hU, isOpen_sigma_iff.mpr (fun i ↦ ?_)⟩
  exact isOpen_radialCollarSet n (hU.preimage (characteristicBoundaryMap C n i).continuous)

theorem isOpen_stepNeighborhood {U : Set (SkeletonLT C n)} (hU : IsOpen U) :
    IsOpen (stepNeighborhood C n U) := by
  apply (isQuotientMap_skeletonStepMap C n).isCoinducing.isOpen_preimage.mp
  rw [preimage_stepNeighborhood]
  exact isOpen_stepNeighborhoodSource C n hU

/-- The explicitly restricted actual attachment quotient on this open set. -/
theorem isQuotientMap_stepNeighborhood_restrict {U : Set (SkeletonLT C n)}
    (hU : IsOpen U) :
    IsQuotientMap ((stepNeighborhood C n U).restrictPreimage (skeletonStepMap C n)) :=
  (isQuotientMap_skeletonStepMap C n).restrictPreimage_isOpen
    (isOpen_stepNeighborhood C n hU)

/-- A convenient coproduct presentation of the same open restricted domain. -/
abbrev StepNeighborhoodDomain (U : Set (SkeletonLT C n)) :=
  U ⊕ (Σ i : RelCWComplex.cell C n, RadialCollar n (stepCollarDirections C n U i))

/-- Inclusion of the actual neighborhood pieces into the original attachment source. -/
def stepNeighborhoodDomainInclusion (U : Set (SkeletonLT C n)) :
    StepNeighborhoodDomain C n U → SkeletonStepDomain C n :=
  Sum.elim (fun x ↦ Sum.inl x.val)
    (fun z ↦ Sum.inr ⟨z.1, collarDiskInclusion n _ z.2⟩)

theorem continuous_stepNeighborhoodDomainInclusion (U : Set (SkeletonLT C n)) :
    Continuous (stepNeighborhoodDomainInclusion C n U) :=
  Continuous.sumElim (continuous_inl.comp continuous_subtype_val)
    (continuous_sigma (fun _i ↦ continuous_inr.comp
      (continuous_sigmaMk.comp (collarDiskInclusion n _).continuous)))

theorem stepNeighborhoodDomainInclusion_mem (U : Set (SkeletonLT C n))
    (x : StepNeighborhoodDomain C n U) :
    stepNeighborhoodDomainInclusion C n U x ∈ stepNeighborhoodSource C n U := by
  cases x with
  | inl x => exact x.property
  | inr z => exact ⟨z.2.val, z.2.property, rfl⟩

/-- The convenient presentation maps onto the genuine next-skeleton open subset. -/
def stepNeighborhoodMap (U : Set (SkeletonLT C n)) :
    StepNeighborhoodDomain C n U → stepNeighborhood C n U := fun z ↦
  ⟨skeletonStepMap C n (stepNeighborhoodDomainInclusion C n U z),
    ⟨_, stepNeighborhoodDomainInclusion_mem C n U z, rfl⟩⟩

theorem stepNeighborhoodMap_surjective (U : Set (SkeletonLT C n)) :
    Function.Surjective (stepNeighborhoodMap C n U) := by
  rintro ⟨y, z, hz, rfl⟩
  cases z with
  | inl x => exact ⟨Sum.inl ⟨x, hz⟩, rfl⟩
  | inr z =>
    obtain ⟨w, hw, he⟩ := hz
    exact ⟨Sum.inr ⟨z.1, ⟨w, hw⟩⟩, Subtype.ext (by
      change skeletonCharacteristicMap C n z.1 w.val = skeletonCharacteristicMap C n z.1 z.2
      rw [he])⟩

/-- The coproduct presentation is a genuine quotient: its source is an open
subspace presentation, followed by the explicit restricted attachment quotient. -/
theorem isQuotientMap_stepNeighborhoodMap {U : Set (SkeletonLT C n)} (hU : IsOpen U) :
    IsQuotientMap (stepNeighborhoodMap C n U) := by
  let F : StepNeighborhoodDomain C n U →
      (skeletonStepMap C n) ⁻¹' stepNeighborhood C n U := fun z ↦
    ⟨stepNeighborhoodDomainInclusion C n U z,
      ⟨_, stepNeighborhoodDomainInclusion_mem C n U z, rfl⟩⟩
  have hF : Continuous F := (continuous_stepNeighborhoodDomainInclusion C n U).subtype_mk _
  have hFo : IsOpenMap F := by
    apply IsOpenMap.subtype_mk
    apply IsOpenMap.sumElim
    · exact isOpenMap_inl.comp hU.isOpenMap_subtype_val
    · apply isOpenMap_sigma.mpr
      intro i
      exact isOpenMap_inr.comp (isOpenMap_sigmaMk.comp
        ((isOpen_characteristicAnnulusSet n).isOpenMap_subtype_val.comp
          (hU.preimage (characteristicBoundaryMap C n i).continuous |>.preimage
            (radialDirection n).continuous).isOpenMap_subtype_val))
  have hFs : Function.Surjective F := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ stepNeighborhoodSource C n U := by
      rw [← preimage_stepNeighborhood]
      exact hz
    cases z with
    | inl x => exact ⟨Sum.inl ⟨x, hz'⟩, rfl⟩
    | inr z =>
      obtain ⟨w, hw, he⟩ := hz'
      exact ⟨Sum.inr ⟨z.1, ⟨w, hw⟩⟩, Subtype.ext (by
        change (Sum.inr ⟨z.1, w.val⟩ : SkeletonStepDomain C n) = Sum.inr ⟨z.1, z.2⟩
        rw [he])⟩
  exact (isQuotientMap_stepNeighborhood_restrict C n hU).comp (hFo.isQuotientMap hF hFs)

end Topology.CWComplex
