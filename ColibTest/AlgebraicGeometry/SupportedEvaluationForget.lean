/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedEvaluationForgetModel
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
universe u

namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
section
open GlobalSectionChangeIndex
variable {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop) [IsOpenImmersion j]
example :
    IsExact (boundedAboveFlatGlobalSupportedSectionModel j).obj.waldhausen.cof
      (boundedAboveFlatGlobalSupportedSectionModel j).obj.waldhausen.weq
      (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.weq (evaluationSmall j) :=
  evaluationSmall_exact j

example : boundedAboveFlatGlobalSupportedSectionModel j ⟶
    asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen j) :=
  evaluationModel j

example : evaluationSmall j ≅ (evaluationModel j).hom.toFunctor :=
  evaluationNormalizationIso j

end
end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation

namespace AlgebraicGeometry.Scheme.Modules
section
variable {Y U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
example :
    IsExact (boundedAboveFlatPerfectSupportedWaldhausen j).cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).weq
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).cof (boundedAboveFlatPerfectWaldhausen
      Y.toRingedSpace).weq
      (tensorCoefficientSupportedForget j) :=
  tensorCoefficientSupportedForget_exact j

example :
    asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen j) ⟶
      asSmallCategory (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace) :=
  tensorCoefficientSupportedForgetModel j

end
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
section
open GlobalSectionChangeIndex
variable {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop) [IsOpenImmersion j]
example :
    (boundedAboveFlatGlobalSupportedForget j).hom.toFunctor ⋙
      GlobalSectionChangeIndex.evaluationSmall X ≅
      evaluationSmall j ⋙ (tensorCoefficientSupportedForgetModel j).hom.toFunctor :=
  evaluationForgetSmallComparisonIso j

example :
    (boundedAboveFlatGlobalSupportedForget j ≫ GlobalSectionChangeIndex.evaluationModel
      X).hom.toFunctor ≅
      (evaluationModel j ≫ tensorCoefficientSupportedForgetModel j).hom.toFunctor :=
  evaluationForgetModelComparisonIso j

end
end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
