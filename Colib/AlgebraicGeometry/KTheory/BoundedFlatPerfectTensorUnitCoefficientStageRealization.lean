/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientStages

/-!
# Whole realization of every genuine finite tensor coefficient cell

The independently prolonged coefficient cells are realized with both original cylinder
isomorphisms. The resulting whole continuous maps are exactly the original structure maps of
the tensor-unit homotopy. The outer time is the coefficient S-row and the inner time is its
forward automorphism edge. No transposition or stable-group detection is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite MonoidalCategory
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- Realize the actual finite coefficient cell, with its original two interval coordinates. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientStageRealization\
    .lean:31"
  "adaptation" "Original levelwise loops, complete coefficient realization and stabilization."]
def tensorUnitPullbackCoefficientStageRealization (k : ℕ) :
    C(unitInterval × (unitInterval × stageSpace k (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace))),
      stageSpace (k + 1) (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))) :=
  ⟨fun z => SSet.toTop.map (tensorUnitPullbackCoefficientStageCylinder f r k)
    ((SSet.realizationCylinderIso
      ((stages k).obj (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)) ⊗ Δ[1])).inv
      ((SSet.realizationCylinderIso
        ((stages k).obj (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)))).inv
          (z.2.2, ULift.up z.2.1), ULift.up z.1)), by fun_prop⟩

/-- The whole realized finite tensor cell agrees with the unchanged original structure track. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientStageRealization\
    .lean:42"
  "adaptation" "Original levelwise loops, complete coefficient realization and stabilization."]
theorem tensorUnitPullbackCoefficientStageRealization_structure (k : ℕ) (s t : unitInterval)
    (x : stageSpace k (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace))) :
    tensorUnitPullbackCoefficientStageRealization f r k (s, (t, x)) =
      (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).structureMap (k + 1)
        ((boundedAboveFlatPerfectTensorUnitHomotopy f r).level (k + 1) (t, x)) s := by
  let A := (stages k).obj (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace))
  let H := stageTransformationCylinder k (tensorUnitPullbackModelTransformation f r)
    (tensorUnitPullbackModelTransformation_weak f r)
  let p := (SSet.realizationCylinderIso (A ⊗ Δ[1])).inv
    ((SSet.realizationCylinderIso A).inv (x, ULift.up t), ULift.up s)
  have h := ConcreteCategory.congr_hom (SSet.realizationCylinderIso_inv_naturality H)
    ((SSet.realizationCylinderIso A).inv (x, ULift.up t), ULift.up s)
  change SSet.toTop.map (H ▷ Δ[1]) p =
    (SSet.realizationCylinderIso _).inv
      (SSet.toTop.map H ((SSet.realizationCylinderIso A).inv (x, ULift.up t)), ULift.up s) at h
  change SSet.toTop.map (tensorUnitPullbackCoefficientStageCylinder f r k) p = _
  rw [tensorUnitPullbackCoefficientStageCylinder_eq, Functor.map_comp]
  change SSet.toTop.map (stageCylinder k (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))
    (SSet.toTop.map (H ▷ Δ[1]) p) = _
  rw [h]
  rfl

/-- Equality of the complete continuous two-time maps, before taking any homotopy class. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientStageRealization\
    .lean:65"
  "adaptation" "Original levelwise loops, complete coefficient realization and stabilization."]
theorem tensorUnitPullbackCoefficientStageRealization_eq (k : ℕ) :
    tensorUnitPullbackCoefficientStageRealization f r k =
      ⟨fun z => (originalPrespectrum
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).structureMap (k + 1)
        ((boundedAboveFlatPerfectTensorUnitHomotopy f r).level (k + 1) (z.2.1, z.2.2)) z.1,
        by fun_prop⟩ := by
  ext z
  exact tensorUnitPullbackCoefficientStageRealization_structure f r k z.1 z.2.1 z.2.2

end AlgebraicGeometry.Scheme.Modules
