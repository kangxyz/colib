/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorModelComparison

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u v u₀ v₀
noncomputable section

example {C : Type u₀} [Category.{v₀} C]
    {D E : Type u} [Category.{v} D] [Category.{v} E]
    (A : C ⥤ D) (B : C ⥤ E) (P Q : D ⥤ E) (i : B ≅ A ⋙ P) (j : P ≅ Q) :
    B ⋙ AsSmall.up ≅ (A ⋙ AsSmall.up) ⋙ asSmallFunctor Q :=
  asSmallWhiskerIso A B P Q i j

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    ((boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q X).op).hom.toFunctor ⋙
      boundedAboveFlatGlobalSectionEvaluation (op (scheme Q (laurent.op.obj X)))) ⋙ AsSmall.up ≅
    evaluationSmall (op (scheme Q X)) ⋙
      (tensorUnitPullbackModelMap (coefficientMap Q X)).hom.toFunctor :=
  tensorMiddleIso Q X

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (internalModelMap Q X).hom.toFunctor ≅ (tensorModelMap Q X).hom.toFunctor :=
  internalTensorModelIso Q X
