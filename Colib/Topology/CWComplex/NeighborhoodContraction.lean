/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.SkeletalNeighborhoodContractions

/-!
# An actual open ambient-contractible neighborhood in a classical CW complex

The union of the constructed skeletal neighborhoods is a subset of the
original CW subtype. Its intersection with every stage skeleton is exactly
the corresponding finite-stage neighborhood. Openness is proved using the
original characteristic quotient, rather than treating skeletal open sets
as ambient open sets.

The exactly compatible finite-stage homotopies define a single ambient
contraction on this union. Its joint continuity is descended through the
actual characteristic quotient restricted to the proved-open union and
multiplied by the compact interval. A coproduct of restricted original disks
is proved to be a continuous open surjective presentation of that restricted
source. Each m-dimensional disk is controlled by the single finite stage m.

No countability, finite dimension, local finiteness, or compact-support
hypothesis is imposed, and the open neighborhood is not given a CW structure.

Adapted from `Quillen/Topology/CWComplex/NeighborhoodContraction.lean` at
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

/-- The actual union inside the original whole-complex subtype. -/
def neighborhoodSet : Set C :=
  {z | ∃ k, ∃ y : SkeletalNeighborhood C n i k, skeletalNeighborhoodToComplex C n i k y = z}

/-- The union carries the actual subspace topology of the original complex. -/
abbrev Neighborhood := ↥(neighborhoodSet C n i)

/-- Exact intersection with each original stage skeleton, including intersections
arising from representatives in strictly later stages. -/
theorem neighborhoodSet_preimage (k : ℕ) :
    (fun y : SkeletonLT C (n + 1 + k) ↦
      (⟨y.val, (CWComplex.skeletonLT C (n + 1 + k : ℕ)).subset_complex y.property⟩ : C)) ⁻¹'
        neighborhoodSet C n i = skeletalNeighborhood C n i k := by
  ext y
  constructor
  · rintro ⟨l, z, hz⟩
    have hval : (skeletalNeighborhoodInclusion C n i (Nat.le_max_right k l) z).val =
        (⟨y.val, CWComplex.skeletonLT_mono
          (by exact_mod_cast Nat.add_le_add_left (Nat.le_max_left k l) (n + 1)) y.property⟩ :
          SkeletonLT C (n + 1 + max k l)) :=
      Subtype.ext (congrArg (fun z : C ↦ z.val) hz)
    have hz' := (skeletalNeighborhoodInclusion C n i (Nat.le_max_right k l) z).property
    rw [hval] at hz'
    exact (Set.ext_iff.mp
      (skeletalNeighborhood_preimage C n i (Nat.le_max_left k l)) y).mp hz'
  · intro hy
    exact ⟨k, ⟨y, hy⟩, rfl⟩

/-- The m-dimensional original disk sees precisely stage m of the construction. -/
theorem neighborhoodSet_characteristic_preimage (m : ℕ) (j : RelCWComplex.cell C m) :
    (fun z : CharacteristicDisk m ↦ characteristicQuotient C ⟨m, j, z⟩) ⁻¹'
        neighborhoodSet C n i =
      (characteristicToSkeleton C j (Nat.lt_add_of_pos_left (Nat.succ_pos n))) ⁻¹'
        skeletalNeighborhood C n i m := by
  ext z
  exact Set.ext_iff.mp (neighborhoodSet_preimage C n i m)
    (characteristicToSkeleton C j (Nat.lt_add_of_pos_left (Nat.succ_pos n)) z)

/-- Ambient openness follows from the original characteristic quotient and the
proved exact finite-stage intersections. -/
theorem isOpen_neighborhoodSet : IsOpen (neighborhoodSet C n i) := by
  apply (isQuotientMap_characteristicQuotient C).isCoinducing.isOpen_preimage.mp
  apply isOpen_sigma_iff.mpr
  intro m
  apply isOpen_sigma_iff.mpr
  intro j
  change IsOpen ((fun z : CharacteristicDisk m ↦ characteristicQuotient C ⟨m, j, z⟩) ⁻¹'
    neighborhoodSet C n i)
  rw [neighborhoodSet_characteristic_preimage]
  exact (isOpen_skeletalNeighborhood C n i m).preimage
    (characteristicToSkeleton C j (Nat.lt_add_of_pos_left (Nat.succ_pos n))).continuous

/-- The prescribed seed point belongs to the actual ambient union. -/
theorem seed_mem_neighborhoodSet (x : CellNeighborhood C n i) :
    cellNeighborhoodToComplex C n i x ∈ neighborhoodSet C n i :=
  ⟨0, x, rfl⟩

/-- The actual inclusion of a finite-stage neighborhood into the ambient union. -/
def neighborhoodStageInclusion (k : ℕ) : C(SkeletalNeighborhood C n i k, Neighborhood C n i) :=
  ⟨fun y ↦ ⟨skeletalNeighborhoodToComplex C n i k y, k, y, rfl⟩,
    (skeletalNeighborhoodToComplex C n i k).continuous.subtype_mk _⟩

/-- The actual ambient subtype inclusion, retained as the initial endpoint. -/
def neighborhoodToComplex : C(Neighborhood C n i, C) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem neighborhoodToComplex_stage (k : ℕ) (y : SkeletalNeighborhood C n i k) :
    neighborhoodToComplex C n i (neighborhoodStageInclusion C n i k y) =
      skeletalNeighborhoodToComplex C n i k y := rfl

/-- A stage containing a specified point of the actual ambient union. -/
def neighborhoodStage (y : Neighborhood C n i) : ℕ := Classical.choose y.property

/-- A chosen stage representative, whose ambient value is proved unchanged below. -/
def neighborhoodRepresentative (y : Neighborhood C n i) :
    SkeletalNeighborhood C n i (neighborhoodStage C n i y) :=
  Classical.choose (Classical.choose_spec y.property)

theorem neighborhoodRepresentative_spec (y : Neighborhood C n i) :
    skeletalNeighborhoodToComplex C n i (neighborhoodStage C n i y)
      (neighborhoodRepresentative C n i y) = y.val :=
  Classical.choose_spec (Classical.choose_spec y.property)

/-- The global contraction evaluated using a chosen finite-stage representative. -/
def neighborhoodContractionFun (x : CellNeighborhood C n i) (p : I × Neighborhood C n i) : C :=
  (skeletalNeighborhoodContraction C n i x (neighborhoodStage C n i p.2)).toHomotopy
    (p.1, neighborhoodRepresentative C n i p.2)

/-- Any finite-stage representative gives exactly the same value, at unchanged time. -/
theorem neighborhoodContractionFun_eq (x : CellNeighborhood C n i) (y : Neighborhood C n i)
    (k : ℕ) (z : SkeletalNeighborhood C n i k)
    (hz : skeletalNeighborhoodToComplex C n i k z = y.val) (t : I) :
    neighborhoodContractionFun C n i x (t, y) =
      (skeletalNeighborhoodContraction C n i x k).toHomotopy (t, z) :=
  skeletalNeighborhoodContraction_eq_of_toComplex_eq C n i x
    (neighborhoodRepresentative C n i y) z
    ((neighborhoodRepresentative_spec C n i y).trans hz.symm) t

/-- The global function restricts literally to each finite-stage contraction. -/
theorem neighborhoodContractionFun_stage (x : CellNeighborhood C n i) (k : ℕ)
    (t : I) (y : SkeletalNeighborhood C n i k) :
    neighborhoodContractionFun C n i x (t, neighborhoodStageInclusion C n i k y) =
      (skeletalNeighborhoodContraction C n i x k).toHomotopy (t, y) :=
  neighborhoodContractionFun_eq C n i x _ k y rfl t

/-- The original closed disk restricted to the actual ambient open neighborhood. -/
def neighborhoodCharacteristicSet (m : ℕ) (j : RelCWComplex.cell C m) :
    Set (CharacteristicDisk m) :=
  (fun z ↦ characteristicQuotient C ⟨m, j, z⟩) ⁻¹' neighborhoodSet C n i

theorem isOpen_neighborhoodCharacteristicSet (m : ℕ) (j : RelCWComplex.cell C m) :
    IsOpen (neighborhoodCharacteristicSet C n i m j) :=
  (isOpen_neighborhoodSet C n i).preimage
    ((continuous_characteristicQuotient C).comp (continuous_sigmaMk.comp continuous_sigmaMk))

/-- The coproduct of the actual restricted original characteristic disks. -/
abbrev NeighborhoodCharacteristicDomain :=
  Σ m : ℕ, Σ j : RelCWComplex.cell C m, ↥(neighborhoodCharacteristicSet C n i m j)

/-- The actual restricted-disk presentation maps to the ambient neighborhood. -/
def neighborhoodCharacteristicMap : NeighborhoodCharacteristicDomain C n i → Neighborhood C n i :=
  fun z ↦ ⟨characteristicQuotient C ⟨z.1, z.2.1, z.2.2.val⟩, z.2.2.property⟩

/-- The restricted original quotient is a quotient because its target is proved open. -/
theorem isQuotientMap_neighborhood_restrict :
    IsQuotientMap ((neighborhoodSet C n i).restrictPreimage (characteristicQuotient C)) :=
  (isQuotientMap_characteristicQuotient C).restrictPreimage_isOpen (isOpen_neighborhoodSet C n i)

/-- The convenient coproduct presentation has the actual restricted-source topology:
its comparison map is continuous, open, and surjective. -/
theorem isQuotientMap_neighborhoodCharacteristicMap :
    IsQuotientMap (neighborhoodCharacteristicMap C n i) := by
  let F : NeighborhoodCharacteristicDomain C n i →
      (characteristicQuotient C) ⁻¹' neighborhoodSet C n i :=
    fun z ↦ ⟨⟨z.1, z.2.1, z.2.2.val⟩, z.2.2.property⟩
  have hF : Continuous F := by
    apply Continuous.subtype_mk
    apply continuous_sigma
    intro m
    apply continuous_sigma
    intro j
    change Continuous (fun z : neighborhoodCharacteristicSet C n i m j ↦
      (⟨m, j, z.val⟩ : CharacteristicDomain C))
    exact continuous_sigmaMk.comp (continuous_sigmaMk.comp continuous_subtype_val)
  have hFo : IsOpenMap F := by
    apply IsOpenMap.subtype_mk
    apply isOpenMap_sigma.mpr
    intro m
    apply isOpenMap_sigma.mpr
    intro j
    exact isOpenMap_sigmaMk.comp (isOpenMap_sigmaMk.comp
      (isOpen_neighborhoodCharacteristicSet C n i m j).isOpenMap_subtype_val)
  have hFs : Function.Surjective F := by
    rintro ⟨⟨m, j, z⟩, hz⟩
    exact ⟨⟨m, j, ⟨z, hz⟩⟩, rfl⟩
  exact (isQuotientMap_neighborhood_restrict C n i).comp (hFo.isQuotientMap hF hFs)

/-- Every restricted m-disk maps continuously into the single fixed stage m. -/
def neighborhoodCharacteristicToStage (m : ℕ) (j : RelCWComplex.cell C m) :
    C(neighborhoodCharacteristicSet C n i m j, SkeletalNeighborhood C n i m) :=
  ⟨fun z ↦ ⟨characteristicToSkeleton C j (Nat.lt_add_of_pos_left (Nat.succ_pos n)) z.val,
    (Set.ext_iff.mp (neighborhoodSet_characteristic_preimage C n i m j) z.val).mp z.property⟩,
    ((characteristicToSkeleton C j (Nat.lt_add_of_pos_left (Nat.succ_pos n))).continuous.comp
      continuous_subtype_val).subtype_mk _⟩

/-- The fixed-stage path on each restricted original disk. -/
def neighborhoodCharacteristicPaths (x : CellNeighborhood C n i)
    (m : ℕ) (j : RelCWComplex.cell C m) :
    C(neighborhoodCharacteristicSet C n i m j, C(I, C)) :=
  ContinuousMap.curry ⟨fun p ↦ (skeletalNeighborhoodContraction C n i x m).toHomotopy
    (p.2, neighborhoodCharacteristicToStage C n i m j p.1),
    (skeletalNeighborhoodContraction C n i x m).toHomotopy.continuous_toFun.comp
      (continuous_snd.prodMk
        ((neighborhoodCharacteristicToStage C n i m j).continuous.comp continuous_fst))⟩

/-- Joint continuity descends through the genuine restricted quotient multiplied
by the compact interval; all source disks factor through fixed finite stages. -/
theorem continuous_neighborhoodContractionFun (x : CellNeighborhood C n i) :
    Continuous (neighborhoodContractionFun C n i x) := by
  apply (isQuotientMap_neighborhoodCharacteristicMap C n i).continuous_lift_prod_right
  let d : C(NeighborhoodCharacteristicDomain C n i, C(I, C)) :=
    ⟨fun z ↦ neighborhoodCharacteristicPaths C n i x z.1 z.2.1 z.2.2,
      continuous_sigma (fun m ↦ continuous_sigma (fun j ↦
        (neighborhoodCharacteristicPaths C n i x m j).continuous))⟩
  have he : (fun p : I × NeighborhoodCharacteristicDomain C n i ↦
      neighborhoodContractionFun C n i x (p.1, neighborhoodCharacteristicMap C n i p.2)) =
      (fun p : I × NeighborhoodCharacteristicDomain C n i ↦ d p.2 p.1) := by
    funext p
    exact neighborhoodContractionFun_eq C n i x (neighborhoodCharacteristicMap C n i p.2)
      p.2.1 (neighborhoodCharacteristicToStage C n i p.2.1 p.2.2.1 p.2.2.2) rfl p.1
  rw [he]
  exact (ContinuousMap.continuous_uncurry_of_continuous d).comp continuous_swap

/-- A jointly continuous ambient contraction of the actual open neighborhood,
with original subtype inclusion and the exact prescribed original seed endpoint. -/
def neighborhoodAmbientContraction (x : CellNeighborhood C n i) :
    (neighborhoodToComplex C n i).Homotopy
      (ContinuousMap.const (Neighborhood C n i) (cellNeighborhoodToComplex C n i x)) where
  toFun := neighborhoodContractionFun C n i x
  continuous_toFun := continuous_neighborhoodContractionFun C n i x
  map_zero_left y := by
    change (skeletalNeighborhoodContraction C n i x (neighborhoodStage C n i y)).toHomotopy
      (0, neighborhoodRepresentative C n i y) = y.val
    rw [skeletalNeighborhoodContraction_zero]
    exact neighborhoodRepresentative_spec C n i y
  map_one_left y :=
    skeletalNeighborhoodContraction_one C n i x (neighborhoodStage C n i y)
      (neighborhoodRepresentative C n i y)

/-- The packaged global homotopy still restricts at exactly the original time. -/
theorem neighborhoodAmbientContraction_stage (x : CellNeighborhood C n i) (k : ℕ)
    (t : I) (y : SkeletalNeighborhood C n i k) :
    neighborhoodAmbientContraction C n i x (t, neighborhoodStageInclusion C n i k y) =
      (skeletalNeighborhoodContraction C n i x k).toHomotopy (t, y) :=
  neighborhoodContractionFun_stage C n i x k t y

end Topology.CWComplex
