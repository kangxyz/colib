/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.SkeletonNeighborhoodExtension
public import Mathlib.Topology.Homotopy.Basic

/-!
# The actual one-step neighborhood deformation

The new collars move radially to their original attaching spheres, while the
old neighborhood is fixed. The retraction and the homotopy are constructed
from those formulas and descended through the actual restricted-open quotient.
Joint continuity explicitly uses this quotient multiplied by the compact
interval. No deformation or retraction certificate is supplied as a premise.

Adapted from `Quillen/Topology/CWComplex/SkeletonNeighborhoodDeformation.lean` at
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
variable (C : Set X) [CWComplex C] (n : ℕ) (U : Set (SkeletonLT C n)) (hU : IsOpen U)

/-- The original inclusion of the old neighborhood into its constructed enlargement. -/
def stepNeighborhoodInclusion : C(U, stepNeighborhood C n U) :=
  ⟨fun x ↦ stepNeighborhoodMap C n U (Sum.inl x),
    (isQuotientMap_stepNeighborhoodMap C n hU).continuous.comp continuous_inl⟩

/-- An actual new collar maps into the constructed neighborhood by its original disk map. -/
def stepNeighborhoodCollarMap (i : RelCWComplex.cell C n) :
    C(RadialCollar n (stepCollarDirections C n U i), stepNeighborhood C n U) :=
  ⟨fun z ↦ stepNeighborhoodMap C n U (Sum.inr ⟨i, z⟩),
    (isQuotientMap_stepNeighborhoodMap C n hU).continuous.comp
      (continuous_inr.comp continuous_sigmaMk)⟩

/-- Each collar retracts to the original attaching value of its unchanged direction. -/
def stepCollarRetraction (i : RelCWComplex.cell C n) :
    C(RadialCollar n (stepCollarDirections C n U i), U) :=
  ⟨fun z ↦ ⟨characteristicBoundaryMap C n i (radialDirection n z.val), z.property⟩,
    ((characteristicBoundaryMap C n i).continuous.comp
      ((radialDirection n).continuous.comp continuous_subtype_val)).subtype_mk _⟩

theorem stepCollarRetraction_boundary (i : RelCWComplex.cell C n)
    (z : stepCollarDirections C n U i) :
    stepCollarRetraction C n U i (stepCollarBoundaryPoint C n U i z) =
      stepOldBoundaryPoint C n U i z := by
  apply Subtype.ext
  change characteristicBoundaryMap C n i (radialDirection n (sphereToAnnulus n z.val)) =
    characteristicBoundaryMap C n i z.val
  rw [radialDirection_sphereToAnnulus]

/-- The actual old identity and actual collar retractions descend to the enlarged neighborhood. -/
def stepNeighborhoodRetraction : C(stepNeighborhood C n U, U) :=
  stepNeighborhoodExtension C n U (ContinuousMap.id U) (stepCollarRetraction C n U) hU
    (stepCollarRetraction_boundary C n U)

@[simp] theorem stepNeighborhoodRetraction_old (x : U) :
    stepNeighborhoodRetraction C n U hU (stepNeighborhoodInclusion C n U hU x) = x :=
  stepNeighborhoodExtension_old C n U _ _ hU _ x

theorem stepNeighborhoodRetraction_collar (i : RelCWComplex.cell C n)
    (z : RadialCollar n (stepCollarDirections C n U i)) :
    stepNeighborhoodRetraction C n U hU (stepNeighborhoodCollarMap C n U hU i z) =
      stepCollarRetraction C n U i z :=
  stepNeighborhoodExtension_collar C n U _ _ hU _ i z

/-- The old neighborhood supplies literal constant paths. -/
def stepNeighborhoodOldPaths : C(U, C(I, stepNeighborhood C n U)) :=
  ContinuousMap.curry ⟨fun p ↦ stepNeighborhoodInclusion C n U hU p.1,
    (stepNeighborhoodInclusion C n U hU).continuous.comp continuous_fst⟩

/-- Each new collar supplies the actual radial path in the original enlarged neighborhood. -/
def stepNeighborhoodCollarPaths (i : RelCWComplex.cell C n) :
    C(RadialCollar n (stepCollarDirections C n U i), C(I, stepNeighborhood C n U)) :=
  ContinuousMap.curry ⟨fun p ↦ stepNeighborhoodCollarMap C n U hU i
    (collarRadialMap n (stepCollarDirections C n U i) (p.2, p.1)),
    (stepNeighborhoodCollarMap C n U hU i).continuous.comp
      ((collarRadialMap n (stepCollarDirections C n U i)).continuous.comp continuous_swap)⟩

/-- Sphere fixation gives equality of the entire prescribed paths on each actual boundary point. -/
theorem stepNeighborhoodPaths_boundary (i : RelCWComplex.cell C n)
    (z : stepCollarDirections C n U i) :
    stepNeighborhoodCollarPaths C n U hU i (stepCollarBoundaryPoint C n U i z) =
      stepNeighborhoodOldPaths C n U hU (stepOldBoundaryPoint C n U i z) := by
  apply ContinuousMap.ext
  intro t
  change stepNeighborhoodCollarMap C n U hU i
      (collarRadialMap n (stepCollarDirections C n U i)
        (t, stepCollarBoundaryPoint C n U i z)) =
    stepNeighborhoodInclusion C n U hU (stepOldBoundaryPoint C n U i z)
  have he : collarRadialMap n (stepCollarDirections C n U i)
      (t, stepCollarBoundaryPoint C n U i z) = stepCollarBoundaryPoint C n U i z :=
    Subtype.ext (annulusRadialMap_sphere n t z.val)
  rw [he]
  exact stepNeighborhoodMap_boundary C n U i z

/-- The constructed path at every enlarged-neighborhood point. -/
def stepNeighborhoodPaths : C(stepNeighborhood C n U, C(I, stepNeighborhood C n U)) :=
  stepNeighborhoodExtension C n U (stepNeighborhoodOldPaths C n U hU)
    (stepNeighborhoodCollarPaths C n U hU) hU (stepNeighborhoodPaths_boundary C n U hU)

/-- Uncurried formula, before endpoint packaging. -/
def stepNeighborhoodDeformationFun (p : I × stepNeighborhood C n U) : stepNeighborhood C n U :=
  stepNeighborhoodPaths C n U hU p.2 p.1

/-- Joint continuity uses the actual restricted-open attachment quotient × I. -/
theorem continuous_stepNeighborhoodDeformationFun :
    Continuous (stepNeighborhoodDeformationFun C n U hU) := by
  apply (isQuotientMap_stepNeighborhoodMap C n hU).continuous_lift_prod_right
  let d : C(StepNeighborhoodDomain C n U, C(I, stepNeighborhood C n U)) :=
    stepNeighborhoodData C n U (stepNeighborhoodOldPaths C n U hU)
      (stepNeighborhoodCollarPaths C n U hU)
  have he : (fun p : I × StepNeighborhoodDomain C n U ↦
      stepNeighborhoodDeformationFun C n U hU (p.1, stepNeighborhoodMap C n U p.2)) =
      (fun p : I × StepNeighborhoodDomain C n U ↦ d p.2 p.1) := by
    funext p
    exact ContinuousMap.congr_fun
      (stepNeighborhoodExtensionFun_map C n U _ _ (stepNeighborhoodPaths_boundary C n U hU) p.2) p.1
  rw [he]
  exact (ContinuousMap.continuous_uncurry_of_continuous d).comp continuous_swap

theorem stepNeighborhoodDeformationFun_old (t : I) (x : U) :
    stepNeighborhoodDeformationFun C n U hU (t, stepNeighborhoodInclusion C n U hU x) =
      stepNeighborhoodInclusion C n U hU x :=
  ContinuousMap.congr_fun (stepNeighborhoodExtension_old C n U _ _ hU
    (stepNeighborhoodPaths_boundary C n U hU) x) t

theorem stepNeighborhoodDeformationFun_collar (t : I) (i : RelCWComplex.cell C n)
    (z : RadialCollar n (stepCollarDirections C n U i)) :
    stepNeighborhoodDeformationFun C n U hU (t, stepNeighborhoodCollarMap C n U hU i z) =
      stepNeighborhoodCollarMap C n U hU i
        (collarRadialMap n (stepCollarDirections C n U i) (t, z)) :=
  ContinuousMap.congr_fun (stepNeighborhoodExtension_collar C n U _ _ hU
    (stepNeighborhoodPaths_boundary C n U hU) i z) t

/-- Every original point is retained at the initial time. -/
theorem stepNeighborhoodDeformationFun_zero (y : stepNeighborhood C n U) :
    stepNeighborhoodDeformationFun C n U hU (0, y) = y := by
  obtain ⟨z, rfl⟩ := stepNeighborhoodMap_surjective C n U y
  cases z with
  | inl x => exact stepNeighborhoodDeformationFun_old C n U hU 0 x
  | inr z =>
    change stepNeighborhoodDeformationFun C n U hU
      (0, stepNeighborhoodCollarMap C n U hU z.1 z.2) = _
    rw [stepNeighborhoodDeformationFun_collar, collarRadialMap_zero]
    rfl

/-- At the final time every collar point reaches its actual original attaching value. -/
theorem stepNeighborhoodDeformationFun_one (y : stepNeighborhood C n U) :
    stepNeighborhoodDeformationFun C n U hU (1, y) =
      stepNeighborhoodInclusion C n U hU (stepNeighborhoodRetraction C n U hU y) := by
  obtain ⟨z, rfl⟩ := stepNeighborhoodMap_surjective C n U y
  cases z with
  | inl x =>
    change stepNeighborhoodDeformationFun C n U hU
      (1, stepNeighborhoodInclusion C n U hU x) =
      stepNeighborhoodInclusion C n U hU
        (stepNeighborhoodRetraction C n U hU (stepNeighborhoodInclusion C n U hU x))
    rw [stepNeighborhoodDeformationFun_old, stepNeighborhoodRetraction_old]
  | inr z =>
    obtain ⟨i, z⟩ := z
    change stepNeighborhoodDeformationFun C n U hU
      (1, stepNeighborhoodCollarMap C n U hU i z) =
      stepNeighborhoodInclusion C n U hU
        (stepNeighborhoodRetraction C n U hU (stepNeighborhoodCollarMap C n U hU i z))
    rw [stepNeighborhoodDeformationFun_collar, stepNeighborhoodRetraction_collar]
    let θ : stepCollarDirections C n U i := ⟨radialDirection n z.val, z.property⟩
    have he : collarRadialMap n (stepCollarDirections C n U i) (1, z) =
        stepCollarBoundaryPoint C n U i θ := Subtype.ext (annulusRadialMap_one n z.val)
    rw [he]
    exact stepNeighborhoodMap_boundary C n U i θ

/-- A strong deformation onto the actual old neighborhood, constructed from the original collars. -/
def stepNeighborhoodDeformation :
    (ContinuousMap.id (stepNeighborhood C n U)).Homotopy
      ((stepNeighborhoodInclusion C n U hU).comp (stepNeighborhoodRetraction C n U hU)) where
  toFun := stepNeighborhoodDeformationFun C n U hU
  continuous_toFun := continuous_stepNeighborhoodDeformationFun C n U hU
  map_zero_left := stepNeighborhoodDeformationFun_zero C n U hU
  map_one_left := stepNeighborhoodDeformationFun_one C n U hU

/-- The entire old neighborhood is fixed at every unchanged time parameter. -/
theorem stepNeighborhoodDeformation_fixed (t : I) (x : U) :
    stepNeighborhoodDeformation C n U hU (t, stepNeighborhoodInclusion C n U hU x) =
      stepNeighborhoodInclusion C n U hU x :=
  stepNeighborhoodDeformationFun_old C n U hU t x

end Topology.CWComplex
