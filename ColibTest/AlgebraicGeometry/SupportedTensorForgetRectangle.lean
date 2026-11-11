/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedTensorForgetRawRectangle
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
universe u

namespace AlgebraicGeometry.Scheme.Modules
section
open GlobalSectionChangeIndex GlobalSupportedSection
variable {A B C : Scheme.OpenPairs.{u}}
example (p : A ⟶ B)
    {K L : (boundedAboveFlatPerfectSupported B.hom).FullSubcategory} (k : K ⟶ L) :
    (tensorCoefficientSupportedForget A.hom).map
        ((boundedAboveFlatPerfectSupportedPullback p).map k) =
      (boundedAboveFlatPerfectPullback p.right).map
        ((tensorCoefficientSupportedForget B.hom).map k) :=
  boundedAboveFlatPerfectSupportedPullback_forget_map p k
end
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
section
open GlobalSectionChangeIndex GlobalSupportedSection
variable {A B C : Scheme.OpenPairs.{u}}
example (p : A ⟶ B)
    (K : (boundedAboveFlatGlobalSectionSupported (X := Opposite.op B.right)
      B.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.hom).map
        ((boundedAboveFlatGlobalSupportedPairReindexEvaluationIso p).hom.app K) =
      (boundedAboveFlatGlobalEvaluationPullbackIso p.right).hom.app K.obj :=
  supportedPairReindexEvaluationIso_forget_hom_app p K
end
end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
section
open GlobalSectionChangeIndex GlobalSupportedSection
variable {A B C : Scheme.OpenPairs.{u}}
variable (p : A ⟶ B)
example :
    boundedAboveFlatGlobalSupportedEvaluation (X := op B.right) B.hom ⋙
      tensorSupportedPairFunctor p ≅
      (boundedAboveFlatGlobalSupportedPairModelMap p).hom.toFunctor ⋙
        boundedAboveFlatGlobalSupportedEvaluation (X := op A.right) A.hom :=
  tensorEvaluationIso p
end
end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation

namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
section
open GlobalSectionChangeIndex GlobalSupportedSection
variable {A B C : Scheme.OpenPairs.{u}}
variable (p : A ⟶ B)
example : (internalModelMap p).hom.toFunctor ≅ (tensorModelMap p).hom.toFunctor
      :=
  internalTensorModelIso p
end
end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation

namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
section
open GlobalSectionChangeIndex GlobalSupportedSection
variable {A B C : Scheme.OpenPairs.{u}}
variable (p : A ⟶ B)
example
    (K : (boundedAboveFlatPerfectSupported B.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.hom).map ((tensorPairUnitor p).inv.app K) =
      (boundedAboveFlatPerfectTensorUnitPullbackIso p.right).inv.app
        ((tensorCoefficientSupportedForget B.hom).obj K) :=
  tensorPairUnitor_forget_inv_app p K
end
end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation

namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
section
open GlobalSectionChangeIndex GlobalSupportedSection
variable {A B C : Scheme.OpenPairs.{u}}
example (p : A ⟶ B)
    (K : (boundedAboveFlatGlobalSectionSupported (X := Opposite.op B.right)
      B.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.hom).map
        ((SupportedTensorEvaluation.tensorEvaluationIso p).hom.app K) =
      (tensorEvaluationIso p.right).hom.app K.obj :=
  tensorEvaluationIso_forget_hom_app p K
end
end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
section
open GlobalSectionChangeIndex GlobalSupportedSection
variable {A B C : Scheme.OpenPairs.{u}}
variable (p : A ⟶ B)
example :
    whiskerLeft (boundedAboveFlatGlobalSupportedEvaluation (X := op B.right) B.hom)
        (tensorSupportedPairForgetIso p).hom ≫
        (isoSquareRoute (evaluationForgetIso (X := op B.right) B.hom)
          (GlobalSectionChangeIndex.tensorEvaluationIso p.right).symm).inv =
      (isoSquareRoute (tensorEvaluationIso p).symm
        (evaluationForgetIso (X := op A.right) A.hom)).inv ≫
        eqToHom (congrArg (fun F => F ⋙ boundedAboveFlatGlobalSectionEvaluation (op A.right))
          (forgetReindexInputSquare p)) :=
  tensorForgetRawRectangle_hom p
end
end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
