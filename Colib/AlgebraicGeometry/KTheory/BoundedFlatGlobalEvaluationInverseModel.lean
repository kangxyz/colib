/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationEquivalence

/-!
# The actual exact inverse of normalized global evaluation

This is the existing categorical evaluation inverse with its prescribed chosen-zero
normalization. The original categorical unit and counit remain explicit; no inverse
in a stable localization is selected.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

/-- The original categorical inverse, normalized only at the chosen zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationInverseModel.lean:26"
  "adaptation" "Original actual exact inverse and prescribed zero normalization"]
def evaluationInverseModel (X : Scheme.{u}ᵒᵖ) :
    asSmallCategory (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace) ⟶
      boundedAboveFlatGlobalSectionModelFunctor.obj X :=
  ExactModelEquivalence.backward (evaluationModelEquivalence X)
    (evaluationSmallEquivalence_inverse_exact X)

/-- The original unit compares actual evaluation and its actual normalized inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationInverseModel.lean:32"
  "adaptation" "Original actual exact inverse and prescribed zero normalization"]
def evaluationInverseUnit (X : Scheme.{u}ᵒᵖ) :
    (evaluationModel X ≫ evaluationInverseModel X).hom.toFunctor ≅
      (𝟙 (boundedAboveFlatGlobalSectionModelFunctor.obj X) :
      boundedAboveFlatGlobalSectionModelFunctor.obj X ⟶
      boundedAboveFlatGlobalSectionModelFunctor.obj X).hom.toFunctor :=
  ExactModelEquivalence.unitIso (evaluationModelEquivalence X) (evaluationModel X).hom.isExact
    (evaluationSmallEquivalence_inverse_exact X) (evaluationModel X).property

/-- The original counit retains the same actual inverse zero normalization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationInverseModel.lean:39"
  "adaptation" "Original actual exact inverse and prescribed zero normalization"]
def evaluationInverseCounit (X : Scheme.{u}ᵒᵖ) :
    (evaluationInverseModel X ≫ evaluationModel X).hom.toFunctor ≅
      (𝟙 (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace)) :
        asSmallCategory (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace) ⟶
          asSmallCategory (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace)).hom.toFunctor :=
  ExactModelEquivalence.counitIso (evaluationModelEquivalence X) (evaluationModel X).hom.isExact
    (evaluationSmallEquivalence_inverse_exact X) (evaluationModel X).property

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

attribute [colib_tag "COL-0548"] evaluationInverseModel
attribute [colib_tag "COL-0548"] evaluationInverseUnit
attribute [colib_tag "COL-0548"] evaluationInverseCounit

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
