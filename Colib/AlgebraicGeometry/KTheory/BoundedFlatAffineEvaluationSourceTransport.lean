/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCoefficients
public import Colib.Topology.Prespectrum.HomotopyTransport

/-!
# Actual source presentations of affine evaluation tracks

The strict section functor and its native model give the same prespectrum object.
The existing evaluation arrow and coefficient track retain their actual native
constructors. Heterogeneous equality records their complete maps before identifying
source-object presentations; no alternative track or source model is introduced.
-/
@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The section prespectrum functor uses the prespectrum of its actual section model. -/
theorem boundedAboveFlatAffineSectionPrespectrumFunctor_obj (R : CommRingCat.{u}) :
    boundedAboveFlatAffineSectionPrespectrumFunctor.obj R =
      prespectrum (boundedAboveFlatAffineSectionModel R) := by
  change prespectrumFunctor.obj (boundedAboveFlatAffineSectionModelFunctor.obj R) = _
  exact congrArg prespectrum
    (show boundedAboveFlatAffineSectionModelFunctor.obj R =
      boundedAboveFlatAffineSectionModel R from rfl)

/-- The existing evaluation arrow is the original map of the native evaluation model. -/
theorem boundedAboveFlatAffineEvaluationPrespectrumMap_heq (R : CommRingCat.{u}) :
    HEq (boundedAboveFlatAffineEvaluationPrespectrumMap R)
      (prespectrumMap (boundedAboveFlatAffineEvaluationModelMap R)) := by
  unfold boundedAboveFlatAffineEvaluationPrespectrumMap
  rfl

/-- The entire actual coefficient level is the original transformation level; the two
existing endpoint-arrow casts do not change any part of its continuous map. -/
theorem boundedAboveFlatAffineEvaluationCoefficientHomotopy_level_heq
    {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ) :
    HEq ((boundedAboveFlatAffineEvaluationCoefficientHomotopy f).level n)
      ((prespectrumTransformationHomotopy
        (F := boundedAboveFlatAffineSectionModelMap f ≫
          boundedAboveFlatAffineEvaluationModelMap S)
        (G := boundedAboveFlatAffineEvaluationModelMap R ≫
          boundedAboveFlatAffinePullbackModelMap f)
        (boundedAboveFlatAffineEvaluationModelIso f).hom
        (fun x ↦ (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace).asSmall.weq_iso _
          (by
            change IsIso ((boundedAboveFlatAffineEvaluationModelIso f).hom.app x)
            infer_instance))).level n) := by
  unfold boundedAboveFlatAffineEvaluationCoefficientHomotopy
  exact heq_of_eq (Homotopy.cast_level
    (prespectrumTransformationHomotopy
      (F := boundedAboveFlatAffineSectionModelMap f ≫
        boundedAboveFlatAffineEvaluationModelMap S)
      (G := boundedAboveFlatAffineEvaluationModelMap R ≫
        boundedAboveFlatAffinePullbackModelMap f)
      (boundedAboveFlatAffineEvaluationModelIso f).hom
      (fun x ↦ (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace).asSmall.weq_iso _
        (by
          change IsIso ((boundedAboveFlatAffineEvaluationModelIso f).hom.app x)
          infer_instance)))
    (prespectrumFunctor.map_comp _ _) (prespectrumFunctor.map_comp _ _) n)

end AlgebraicGeometry.Scheme.Modules
