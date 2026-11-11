/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationModel
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumPullback
public import Colib.CategoryTheory.Waldhausen.AsSmall.Whiskering
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumIntertwiningHomotopy

/-! # Original geometric evaluation comparison with both chosen-zero normalizations -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

/-- The original raw geometric model map with its actual zero normalization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationNaturality.lean:21"
  "adaptation" "Original full evaluation comparison and both zero normalizations"]
def evaluationRawMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    asSmallCategory (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace) ⟶ asSmallCategory
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) :=
  asSmallCategoryMap _ _ (boundedAboveFlatPerfectPullback_isExact f).rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)

/-- The actual raw normalization isomorphism before common-universe lifting. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationNaturality.lean:27"
  "adaptation" "Original full evaluation comparison and both zero normalizations"]
def evaluationRawNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  CategoryTheory.rebaseFunctorIso (boundedAboveFlatPerfectPullback f)
    (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).zero (boundedAboveFlatPerfectWaldhausen
      X.toRingedSpace).zero
    (((boundedAboveFlatPerfectPullback_isExact f).zero (boundedAboveFlatPerfectWaldhausen
      Y.toRingedSpace).isZero).iso
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).isZero)

/-- Lift the actual evaluation transition and original raw zero normalization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationNaturality.lean:34"
  "adaptation" "Original full evaluation comparison and both zero normalizations"]
def evaluationMiddleIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor ⋙
      boundedAboveFlatGlobalSectionEvaluation (Opposite.op X)) ⋙ AsSmall.up ≅
      evaluationSmall (Opposite.op Y) ⋙ (evaluationRawMap f).hom.toFunctor :=
  asSmallWhiskerIso (boundedAboveFlatGlobalSectionEvaluation (Opposite.op Y))
    ((boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor ⋙
      boundedAboveFlatGlobalSectionEvaluation (Opposite.op X))
    (boundedAboveFlatPerfectPullback f) _ (boundedAboveFlatGlobalEvaluationPullbackIso f).symm
    (evaluationRawNormalization f)

/-- Preserve the complete original geometric comparison rather than declaring a strict square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationNaturality.lean:43"
  "adaptation" "Original full evaluation comparison and both zero normalizations"]
def evaluationComparisonIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatGlobalSectionModelFunctor.map f.op ≫ evaluationModel (Opposite.op
      X)).hom.toFunctor ≅
      (evaluationModel (Opposite.op Y) ≫ evaluationRawMap f).hom.toFunctor :=
  isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor
      (evaluationNormalizationIso (Opposite.op X)).symm ≪≫
    (Functor.associator (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor
      (boundedAboveFlatGlobalSectionEvaluation (Opposite.op X)) AsSmall.up).symm ≪≫
    evaluationMiddleIso f ≪≫
    isoWhiskerRight (evaluationNormalizationIso (Opposite.op Y)) _

/-- The original comparison keeps every spectrum level and its independent structure coordinate. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationNaturality.lean:54"
  "adaptation" "Original full evaluation comparison and both zero normalizations"]
def evaluationComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Homotopy
      (prespectrumMap (boundedAboveFlatGlobalSectionModelFunctor.map f.op) ≫ prespectrumMap
      (evaluationModel (Opposite.op X)))
      (prespectrumMap (evaluationModel (Opposite.op Y)) ≫ prespectrumMap (evaluationRawMap f)) :=
  (prespectrumTransformationHomotopy
    (V := boundedAboveFlatGlobalSectionModelFunctor.obj (Opposite.op Y))
    (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))
    (F := boundedAboveFlatGlobalSectionModelFunctor.map f.op ≫ evaluationModel (Opposite.op X))
    (G := evaluationModel (Opposite.op Y) ≫ evaluationRawMap f)
    (evaluationComparisonIso f).hom
    (fun A ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _
      (inferInstanceAs (IsIso ((evaluationComparisonIso f).app A).hom)))).cast
      (prespectrumFunctor.map_comp _ _) (prespectrumFunctor.map_comp _ _)

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

attribute [colib_tag "COL-0548"] evaluationComparison

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
