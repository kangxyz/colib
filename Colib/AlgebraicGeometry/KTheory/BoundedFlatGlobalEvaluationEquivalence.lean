/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationNaturality
public import Colib.KTheory.Waldhausen.Iterated.ExactModelEquivalence

/-!
# Exact categorical inverse and stability of global evaluation

The original global evaluation has its actual exact categorical inverse. The existing
levelwise homotopy inverse theorem proves stability without a new assumption. This file
migrates the first four declarations of the original stable comparison owner. Its six
localized and K-group naturality results are not asserted here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.GrothendieckSections CategoryTheory.GrothendieckZeroSections
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

/-- Original global evaluation, followed by the actual common-universe equivalence. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationStableComparison.lean:33"
  "adaptation" "Original actual exact inverse and prescribed zero normalization"]
def evaluationSmallEquivalence (X : Scheme.{u}ᵒᵖ) :
    (boundedAboveFlatGlobalSectionModelFunctor.obj X).obj.Obj ≌ AsSmall.{0}
      ((boundedAboveFlatPerfectComplex X.unop.toRingedSpace).FullSubcategory) :=
  (originalEvaluationEquivalence boundedAboveFlatPerfectPseudofunctor X).trans AsSmall.equiv

/-- The actual inverse lowers the universe and uses the original evaluation inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationStableComparison.lean:38"
  "adaptation" "Original actual exact inverse and prescribed zero normalization"]
theorem evaluationSmallEquivalence_inverse_exact (X : Scheme.{u}ᵒᵖ) :
    IsExact (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).asSmall.cof
      (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).asSmall.weq
      (boundedAboveFlatGlobalSectionModelFunctor.obj X).obj.waldhausen.cof
      (boundedAboveFlatGlobalSectionModelFunctor.obj X).obj.waldhausen.weq
      (evaluationSmallEquivalence X).inverse :=
  (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).asSmall_down_exact.comp
    (Structure.ofEquivalence_inverse_exact _ _ _ (boundedAboveFlatGlobalFiberZero_isZero X))

/-- The genuine equivalence retains the already chosen normalized evaluation functor. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationStableComparison.lean:47"
  "adaptation" "Original actual exact inverse and prescribed zero normalization"]
def evaluationModelEquivalence (X : Scheme.{u}ᵒᵖ) :
    (boundedAboveFlatGlobalSectionModelFunctor.obj X).obj.Obj ≌ (asSmallCategory
      (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace)).obj.Obj :=
  (evaluationSmallEquivalence X).changeFunctor (evaluationNormalizationIso X)

/-- The original normalized evaluation has an actual exact categorical inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationStableComparison.lean:52"
  "adaptation" "Original actual exact inverse and prescribed zero normalization"]
theorem evaluationModel_isStableEquivalence (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (prespectrumMap (evaluationModel X)) :=
  ExactModelEquivalence.isStableEquivalence (evaluationModelEquivalence X)
    (evaluationModel X).hom.isExact (evaluationSmallEquivalence_inverse_exact X)
    (evaluationModel X).property

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

attribute [colib_tag "COL-0548"] evaluationModel_isStableEquivalence

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
