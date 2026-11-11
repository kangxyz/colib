/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedTensorForgetModelRectangle
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
open GlobalSectionChangeIndex GlobalSupportedSection
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)

example :
    whiskerLeft (boundedAboveFlatGlobalSupportedEvaluation (X := op B.right) B.hom)
        (tensorForgetNormalizedIso p).hom ≫ (tensorForgetNormalizedRightRoute p).inv =
      (tensorForgetNormalizedLeftRoute p).inv ≫
        eqToHom (congrArg (fun F => F ⋙ boundedAboveFlatGlobalSectionEvaluation (op A.right))
          (forgetReindexInputSquare p)) :=
  tensorForgetNormalizedRectangle_hom p

example :
    (boundedAboveFlatGlobalSupportedPairModelMap p).hom.toFunctor ⋙ evaluationSmall (X := op
      A.right) A.hom ≅
      evaluationSmall (X := op B.right) B.hom ⋙ (tensorSupportedPairModelMap
      p).hom.toFunctor :=
  forgetSupportedTensorSmallIso p

example :
    whiskerLeft (evaluationSmall (X := op B.right) B.hom)
        (tensorForgetModelIso p).hom ≫ (tensorForgetSmallRightRoute p).inv =
      (tensorForgetSmallLeftRoute p).inv ≫
        eqToHom (congrArg (fun F => F ⋙ GlobalSectionChangeIndex.evaluationSmall
          (op A.right)) (forgetReindexInputSquare p)) :=
  tensorForgetSmallRectangle_hom p

example :
    internalTensorModelIso p = isoSquareConjugate (forgetSupportedTensorSmallIso p)
      (evaluationNormalizationIso (X := op B.right) B.hom)
      (evaluationNormalizationIso (X := op A.right) A.hom) :=
  internalTensorModelIso_forgetSmall p

example :
    whiskerLeft (evaluationModel (X := op B.right) B.hom).hom.toFunctor
        (tensorForgetModelIso p).hom ≫ (tensorForgetModelRightRoute p).inv =
      (tensorForgetModelLeftRoute p).inv ≫
        eqToHom (congrArg (fun F => F ⋙
          (GlobalSectionChangeIndex.evaluationModel (op A.right)).hom.toFunctor)
          (forgetReindexInputSquare p)) :=
  tensorForgetModelRectangle_hom p

example :
    isoWhiskerLeft (evaluationModel (X := op B.right) B.hom).hom.toFunctor
        (tensorForgetModelIso p) ≪≫ (tensorForgetModelRightRoute p).symm =
      (tensorForgetModelLeftRoute p).symm ≪≫
        eqToIso (congrArg (fun F => F ⋙
          (GlobalSectionChangeIndex.evaluationModel (op A.right)).hom.toFunctor)
          (forgetReindexInputSquare p)) :=
  tensorForgetModelRectangle p

end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
