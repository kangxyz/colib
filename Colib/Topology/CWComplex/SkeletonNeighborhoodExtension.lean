/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.SkeletonNeighborhood

/-!
# Descent from the original open-skeleton neighborhood pieces

Prescribed maps on the old neighborhood and its actual disk collars descend
through the proved open restricted attachment quotient when they agree on
their original attaching-sphere points. All fiberwise compatibility is proved
from the actual characteristic maps; it is not an additional input.

Adapted from `Quillen/Topology/CWComplex/SkeletonNeighborhoodExtension.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

open Topology
noncomputable section
open Set Metric
universe u v
namespace Topology.CWComplex
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C] (n : ℕ) (U : Set (SkeletonLT C n))

/-- The supplied sphere directions as literal points of their own collar. -/
def stepCollarBoundaryPoint (i : RelCWComplex.cell C n) :
    C(stepCollarDirections C n U i, RadialCollar n (stepCollarDirections C n U i)) := by
  let f : stepCollarDirections C n U i → RadialCollar n (stepCollarDirections C n U i) :=
    fun z ↦ ⟨sphereToAnnulus n z.val, by
      change radialDirection n (sphereToAnnulus n z.val) ∈ stepCollarDirections C n U i
      simpa only [radialDirection_sphereToAnnulus] using z.property⟩
  have hf : Continuous (fun z : stepCollarDirections C n U i ↦ sphereToAnnulus n z.val) :=
    (sphereToAnnulus n).continuous.comp continuous_subtype_val
  exact ⟨f, hf.subtype_mk _⟩

/-- The same boundary point, in the actual old neighborhood. -/
def stepOldBoundaryPoint (i : RelCWComplex.cell C n) : C(stepCollarDirections C n U i, U) :=
  ⟨fun z ↦ ⟨characteristicBoundaryMap C n i z.val, z.property⟩,
    ((characteristicBoundaryMap C n i).continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The two displayed boundary points have exactly the same original quotient image. -/
theorem stepNeighborhoodMap_boundary (i : RelCWComplex.cell C n)
    (z : stepCollarDirections C n U i) :
    stepNeighborhoodMap C n U (Sum.inr ⟨i, stepCollarBoundaryPoint C n U i z⟩) =
      stepNeighborhoodMap C n U (Sum.inl (stepOldBoundaryPoint C n U i z)) := by
  apply Subtype.ext
  exact skeletonCharacteristicMap_boundary C n i z.val

variable {Y : Type v} [TopologicalSpace Y]
variable (a : C(U, Y))
variable (b : ∀ i : RelCWComplex.cell C n, C(RadialCollar n (stepCollarDirections C n U i), Y))

/-- The original old/collar values before their genuine quotient descent. -/
def stepNeighborhoodData : C(StepNeighborhoodDomain C n U, Y) :=
  ⟨Sum.elim a (fun z ↦ b z.1 z.2),
    Continuous.sumElim a.continuous (continuous_sigma (fun i ↦ (b i).continuous))⟩

/-- A collar point whose characteristic image is old is its own literal sphere point. -/
theorem collar_value_eq_old
    (hab : ∀ i z, b i (stepCollarBoundaryPoint C n U i z) = a (stepOldBoundaryPoint C n U i z))
    (i : RelCWComplex.cell C n) (z : RadialCollar n (stepCollarDirections C n U i))
    (hz : RelCWComplex.map n i z.val.val ∈ (CWComplex.skeletonLT C n : Set X)) :
    ∃ u : U, u.val.val = RelCWComplex.map n i z.val.val ∧ b i z = a u := by
  let θ : CharacteristicSphere n :=
    ⟨z.val.val.val, (characteristic_mem_previous_iff C n i z.val.val).mp hz⟩
  have he : z.val = sphereToAnnulus n θ := Subtype.ext rfl
  have hθ : θ ∈ stepCollarDirections C n U i := by
    have h := z.property
    change radialDirection n z.val ∈ stepCollarDirections C n U i at h
    simpa only [he, radialDirection_sphereToAnnulus] using h
  let θ' : stepCollarDirections C n U i := ⟨θ, hθ⟩
  have hz' : stepCollarBoundaryPoint C n U i θ' = z := Subtype.ext he.symm
  refine ⟨stepOldBoundaryPoint C n U i θ', rfl, ?_⟩
  rw [← hz']
  exact hab i θ'

/-- Equal new-collar images force equal values: old collisions use the boundary
agreement, and interior collisions use the original partial-equivalence injection. -/
theorem collar_values_eq_of_same_image
    (hab : ∀ i z, b i (stepCollarBoundaryPoint C n U i z) = a (stepOldBoundaryPoint C n U i z))
    (i j : RelCWComplex.cell C n)
    (z : RadialCollar n (stepCollarDirections C n U i))
    (w : RadialCollar n (stepCollarDirections C n U j))
    (he : RelCWComplex.map n i z.val.val = RelCWComplex.map n j w.val.val) : b i z = b j w := by
  by_cases hz : RelCWComplex.map n i z.val.val ∈ (CWComplex.skeletonLT C n : Set X)
  · have hw : RelCWComplex.map n j w.val.val ∈ (CWComplex.skeletonLT C n : Set X) := he ▸ hz
    obtain ⟨u, hu, hzu⟩ := collar_value_eq_old C n U a b hab i z hz
    obtain ⟨v, hv, hwv⟩ := collar_value_eq_old C n U a b hab j w hw
    exact hzu.trans ((congrArg a (Subtype.ext (Subtype.ext (hu.trans (he.trans hv.symm))))).trans
      hwv.symm)
  · have hw : RelCWComplex.map n j w.val.val ∉ (CWComplex.skeletonLT C n : Set X) := by
      simpa only [← he] using hz
    have hzb : z.val.val.val ∈ ball (0 : Fin n → ℝ) 1 := by
      rw [← closedBall_sdiff_sphere]
      exact ⟨z.val.val.property,
        fun hs ↦ hz ((characteristic_mem_previous_iff C n i z.val.val).mpr hs)⟩
    have hwb : w.val.val.val ∈ ball (0 : Fin n → ℝ) 1 := by
      rw [← closedBall_sdiff_sphere]
      exact ⟨w.val.val.property,
        fun hs ↦ hw ((characteristic_mem_previous_iff C n j w.val.val).mpr hs)⟩
    have hij : i = j := by
      by_contra hne
      have hd := RelCWComplex.disjoint_openCell_of_ne
        (by simpa using hne : (⟨n, i⟩ : Σ m, RelCWComplex.cell C m) ≠ ⟨n, j⟩)
      exact hd.notMem_of_mem_left ⟨z.val.val, hzb, rfl⟩ ⟨w.val.val, hwb, he.symm⟩
    subst j
    have hzw : z = w := Subtype.ext (Subtype.ext (Subtype.ext
      ((RelCWComplex.map n i).injOn (by rwa [RelCWComplex.source_eq])
        (by rwa [RelCWComplex.source_eq]) he)))
    exact congrArg (b i) hzw

/-- All fibers of the actual open attachment quotient respect the displayed values. -/
theorem stepNeighborhoodData_fiberwise
    (hab : ∀ i z, b i (stepCollarBoundaryPoint C n U i z) = a (stepOldBoundaryPoint C n U i z))
    (x y : StepNeighborhoodDomain C n U)
    (h : stepNeighborhoodMap C n U x = stepNeighborhoodMap C n U y) :
    stepNeighborhoodData C n U a b x = stepNeighborhoodData C n U a b y := by
  have he := congrArg (fun z : stepNeighborhood C n U ↦ z.val.val) h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg a (Subtype.ext (Subtype.ext he))
    | inr y =>
      obtain ⟨i, z⟩ := y
      change x.val.val = RelCWComplex.map n i z.val.val at he
      obtain ⟨u, hu, hz⟩ := collar_value_eq_old C n U a b hab i z (he ▸ x.val.property)
      exact (congrArg a (Subtype.ext (Subtype.ext (he.trans hu.symm)))).trans hz.symm
  | inr x =>
    obtain ⟨i, z⟩ := x
    cases y with
    | inl y =>
      change RelCWComplex.map n i z.val.val = y.val.val at he
      obtain ⟨u, hu, hz⟩ := collar_value_eq_old C n U a b hab i z (he.symm ▸ y.val.property)
      exact hz.trans (congrArg a (Subtype.ext (Subtype.ext (hu.trans he))))
    | inr y =>
      obtain ⟨j, w⟩ := y
      exact collar_values_eq_of_same_image C n U a b hab i j z w he

/-- Choose only a representative of the proved-surjective actual quotient. -/
def stepNeighborhoodExtensionFun (y : stepNeighborhood C n U) : Y :=
  stepNeighborhoodData C n U a b (Classical.choose (stepNeighborhoodMap_surjective C n U y))

theorem stepNeighborhoodExtensionFun_map
    (hab : ∀ i z, b i (stepCollarBoundaryPoint C n U i z) = a (stepOldBoundaryPoint C n U i z))
    (x : StepNeighborhoodDomain C n U) :
    stepNeighborhoodExtensionFun C n U a b (stepNeighborhoodMap C n U x) =
      stepNeighborhoodData C n U a b x :=
  stepNeighborhoodData_fiberwise C n U a b hab _ x
    (Classical.choose_spec (stepNeighborhoodMap_surjective C n U (stepNeighborhoodMap C n U x)))

/-- Descent is continuous for the actual open restricted attachment topology. -/
def stepNeighborhoodExtension (hU : IsOpen U)
    (hab : ∀ i z, b i (stepCollarBoundaryPoint C n U i z) = a (stepOldBoundaryPoint C n U i z)) :
    C(stepNeighborhood C n U, Y) where
  toFun := stepNeighborhoodExtensionFun C n U a b
  continuous_toFun := by
    apply (isQuotientMap_stepNeighborhoodMap C n hU).continuous_iff.mpr
    have he : stepNeighborhoodExtensionFun C n U a b ∘ stepNeighborhoodMap C n U =
        stepNeighborhoodData C n U a b := funext (stepNeighborhoodExtensionFun_map C n U a b hab)
    rw [he]
    exact (stepNeighborhoodData C n U a b).continuous

theorem stepNeighborhoodExtension_old (hU : IsOpen U)
    (hab : ∀ i z, b i (stepCollarBoundaryPoint C n U i z) = a (stepOldBoundaryPoint C n U i z))
    (x : U) :
    stepNeighborhoodExtension C n U a b hU hab (stepNeighborhoodMap C n U (Sum.inl x)) = a x :=
  stepNeighborhoodExtensionFun_map C n U a b hab (Sum.inl x)

theorem stepNeighborhoodExtension_collar (hU : IsOpen U)
    (hab : ∀ i z, b i (stepCollarBoundaryPoint C n U i z) = a (stepOldBoundaryPoint C n U i z))
    (i : RelCWComplex.cell C n) (z : RadialCollar n (stepCollarDirections C n U i)) :
    stepNeighborhoodExtension C n U a b hU hab (stepNeighborhoodMap C n U (Sum.inr ⟨i, z⟩)) =
      b i z :=
  stepNeighborhoodExtensionFun_map C n U a b hab (Sum.inr ⟨i, z⟩)

end Topology.CWComplex
