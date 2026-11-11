/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientCylinder
public import Colib.KTheory.Waldhausen.Iterated.HomotopyTransport

/-!
# Realization of the actual fixed tensor coefficient cell

Realize the independently constructed and zero-normalized first coefficient cell using the
original two cylinder isomorphisms. Its whole value is the original suspension row applied to the
original normalized tensor-unit track. The coefficient object-row time and the forward unit
nerve time stay in their specified order. The original small-model transport identifies the
inner track with the existing tensor-unit prespectrum homotopy at level one.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite MonoidalCategory
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
      CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- Realize the actual fixed coefficient cell: outer time is its S-row, inner time its unit edge. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientRealization.lean:33"
  "adaptation" "Original actual coefficient cylinder and ordered two-parameter realization."]
def tensorUnitPullbackCoefficientRealization :
    C(unitInterval × (unitInterval × (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).Delooping),
      |doubleDiagonal (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)|) :=
  ⟨fun z => SSet.toTop.map (tensorUnitPullbackCoefficientCylinder f r)
    ((SSet.realizationCylinderIso
      (sSet (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).weq ⊗ Δ[1])).inv
      ((SSet.realizationCylinderIso
        (sSet (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).weq)).inv
          (z.2.2, ULift.up z.2.1), ULift.up z.1)), by fun_prop⟩

/-- The full realized cell is the original suspension row of the original normalized tensor track.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientRealization.lean:45"
  "adaptation" "Original actual coefficient cylinder and ordered two-parameter realization."]
theorem tensorUnitPullbackCoefficientRealization_eq (s t : unitInterval)
    (x : (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).Delooping) :
    tensorUnitPullbackCoefficientRealization f r (s, (t, x)) =
      loopStructureMap (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
        (weakNaturalTransformationRealizationHomotopy
          (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace) (boundedAboveFlatPerfectWaldhausen
      X.toRingedSpace)
          (boundedAboveFlatPerfectTensorUnitPullback_exact f).rebase
          (boundedAboveFlatPerfectTensorUnitPullback_exact f).rebase
          (normalizedWeakTransformation (boundedAboveFlatPerfectTensorUnitPullback_exact f)
            (boundedAboveFlatPerfectTensorUnitPullback_exact f)
            (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom)
          (normalizedWeakTransformation_weak (boundedAboveFlatPerfectTensorUnitPullback_exact f)
            (boundedAboveFlatPerfectTensorUnitPullback_exact f)
            (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom
            (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _
      inferInstance)) (t, x)) s := by
  let A := sSet (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).weq
  let H := tensorUnitPullbackNormalizedCylinder f r
  let p := (SSet.realizationCylinderIso (A ⊗ Δ[1])).inv
    ((SSet.realizationCylinderIso A).inv (x, ULift.up t), ULift.up s)
  have h := ConcreteCategory.congr_hom (SSet.realizationCylinderIso_inv_naturality H)
    ((SSet.realizationCylinderIso A).inv (x, ULift.up t), ULift.up s)
  change SSet.toTop.map (H ▷ Δ[1]) p =
    (SSet.realizationCylinderIso _).inv
      (SSet.toTop.map H ((SSet.realizationCylinderIso A).inv (x, ULift.up t)), ULift.up s) at h
  change SSet.toTop.map (tensorUnitPullbackCoefficientCylinder f r) p = _
  rw [tensorUnitPullbackCoefficientCylinder_eq, Functor.map_comp]
  change SSet.toTop.map (suspensionCylinder (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))
    (SSet.toTop.map (H ▷ Δ[1]) p) = _
  rw [h]
  rfl

/-- The inner coefficient-edge track is the unchanged original tensor prespectrum track. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientRealization.lean:77"
  "adaptation" "Original actual coefficient cylinder and ordered two-parameter realization."]
theorem tensorUnitPullbackNormalizedRealization_track (t : unitInterval)
    (x : (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).Delooping) :
    (boundedAboveFlatPerfectTensorUnitHomotopy f r).level 1
        (t, (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).asSmallDeloopingHomeomorph x) =
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmallDeloopingHomeomorph
        (weakNaturalTransformationRealizationHomotopy
          (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace) (boundedAboveFlatPerfectWaldhausen
      X.toRingedSpace)
          (boundedAboveFlatPerfectTensorUnitPullback_exact f).rebase
          (boundedAboveFlatPerfectTensorUnitPullback_exact f).rebase
          (normalizedWeakTransformation (boundedAboveFlatPerfectTensorUnitPullback_exact f)
            (boundedAboveFlatPerfectTensorUnitPullback_exact f)
            (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom)
          (normalizedWeakTransformation_weak (boundedAboveFlatPerfectTensorUnitPullback_exact f)
            (boundedAboveFlatPerfectTensorUnitPullback_exact f)
            (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom
            (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _
      inferInstance)) (t, x)) :=
  originalPrespectrumTransformationHomotopy_level_one _ _
    (boundedAboveFlatPerfectTensorUnitPullback_exact f).rebase
    (boundedAboveFlatPerfectTensorUnitPullback_exact f).rebase _ _
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) (CategoryTheory.rebaseFunctor_obj_base _ _ _
      _) t x

/-- The realized fixed cell retains both times and the original prespectrum-track normalization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientRealization.lean:99"
  "adaptation" "Original actual coefficient cylinder and ordered two-parameter realization."]
theorem tensorUnitPullbackCoefficientRealization_track (s t : unitInterval)
    (x : (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).Delooping) :
    tensorUnitPullbackCoefficientRealization f r (s, (t, x)) =
      loopStructureMap (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
        ((boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmallDeloopingHomeomorph.symm
          ((boundedAboveFlatPerfectTensorUnitHomotopy f r).level 1
            (t, (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).asSmallDeloopingHomeomorph
      x))) s := by
  rw [tensorUnitPullbackNormalizedRealization_track, Homeomorph.symm_apply_apply]
  exact tensorUnitPullbackCoefficientRealization_eq f r s t x

end AlgebraicGeometry.Scheme.Modules
