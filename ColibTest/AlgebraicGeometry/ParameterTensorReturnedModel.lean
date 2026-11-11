/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorReturnedModel

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
noncomputable section
open Topology.LoopPrespectrum Opposite
open AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
universe u v u₁ v₁

example {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (A : D ⥤ E) (B : E ⥤ D) (G : C ⥤ E)
    (j : A ⋙ B ≅ 𝟭 D) (e : F ⋙ A ≅ G) : F ≅ G ⋙ B :=
  returnIso F A B G j e

example
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (A : D ⥤ E) (B : E ⥤ D) (G : C ⥤ E)
    (j : A ⋙ B ≅ 𝟭 D) (e : F ⋙ A ≅ G)
    (η : F ⟶ F) (θ : G ⟶ G)
    (h : whiskerRight η A ≫ e.hom = e.hom ≫ θ) :
    η ≫ (returnIso F A B G j e).hom =
      (returnIso F A B G j e).hom ≫ whiskerRight θ B :=
  returnIso_intertwining F A B G j e η θ h

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q X).op).hom.toFunctor ≅
      (returnedTensorModel Q X).hom.toFunctor :=
  returnedTensorIso Q X

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (onFunctor (boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q X).op).hom.toFunctor
      (boundedAboveFlatGlobalSectionUnit (op (scheme Q (laurent.op.obj X)))
        (ParameterLaurentUnit.projectedLaurentScalar Q X))).hom ≫
        (returnedTensorIso Q X).hom =
      (returnedTensorIso Q X).hom ≫ returnedTensorUnit Q X :=
  returnedTensorIso_unit Q X

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    returnedTensorModel Q X = tensorModelMap Q X ≫
      evaluationInverseModel (op (scheme Q (laurent.op.obj X))) := rfl

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    returnedTensorUnit Q X = whiskerRight (tensorModelUnit Q X)
      (evaluationInverseModel (op (scheme Q (laurent.op.obj X)))).hom.toFunctor := rfl
