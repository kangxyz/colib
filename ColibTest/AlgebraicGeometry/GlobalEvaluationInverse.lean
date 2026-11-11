/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationInverseModel

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
noncomputable section
open Topology.LoopPrespectrum
universe u v u₁ v₁

example (X : Scheme.{u}ᵒᵖ) :
    (boundedAboveFlatGlobalSectionModelFunctor.obj X).obj.Obj ≌ AsSmall.{0}
      ((boundedAboveFlatPerfectComplex X.unop.toRingedSpace).FullSubcategory) :=
  evaluationSmallEquivalence X

example (X : Scheme.{u}ᵒᵖ) :
    IsExact (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).asSmall.cof
      (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).asSmall.weq
      (boundedAboveFlatGlobalSectionModelFunctor.obj X).obj.waldhausen.cof
      (boundedAboveFlatGlobalSectionModelFunctor.obj X).obj.waldhausen.weq
      (evaluationSmallEquivalence X).inverse :=
  evaluationSmallEquivalence_inverse_exact X

example (X : Scheme.{u}ᵒᵖ) :
    (boundedAboveFlatGlobalSectionModelFunctor.obj X).obj.Obj ≌ (asSmallCategory
      (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace)).obj.Obj :=
  evaluationModelEquivalence X

example (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (prespectrumMap (evaluationModel X)) :=
  evaluationModel_isStableEquivalence X

example (X : Scheme.{u}ᵒᵖ) :
    asSmallCategory (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace) ⟶
      boundedAboveFlatGlobalSectionModelFunctor.obj X :=
  evaluationInverseModel X

example (X : Scheme.{u}ᵒᵖ) :
    (evaluationModel X ≫ evaluationInverseModel X).hom.toFunctor ≅
      (𝟙 (boundedAboveFlatGlobalSectionModelFunctor.obj X) :
      boundedAboveFlatGlobalSectionModelFunctor.obj X ⟶
      boundedAboveFlatGlobalSectionModelFunctor.obj X).hom.toFunctor :=
  evaluationInverseUnit X

example (X : Scheme.{u}ᵒᵖ) :
    (evaluationInverseModel X ≫ evaluationModel X).hom.toFunctor ≅
      (𝟙 (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace)) :
        asSmallCategory (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace) ⟶
          asSmallCategory (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace)).hom.toFunctor :=
  evaluationInverseCounit X

