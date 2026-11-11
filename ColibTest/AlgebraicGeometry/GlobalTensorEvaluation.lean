/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationModel

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
noncomputable section
universe u v u₁ v₁

example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedAboveFlatGlobalSectionEvaluation (Opposite.op Y) ⋙
      boundedAboveFlatPerfectTensorUnitPullback f ≅
      (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor ⋙
      boundedAboveFlatGlobalSectionEvaluation (Opposite.op X) :=
  tensorEvaluationIso f

example {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    Functor.whiskerLeft (boundedAboveFlatGlobalSectionEvaluation (Opposite.op Y))
        (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom ≫
      (tensorEvaluationIso f).hom =
    (tensorEvaluationIso f).hom ≫
      Functor.whiskerRight
        (Functor.whiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor
          (boundedAboveFlatGlobalSectionUnit (Opposite.op X) r).hom)
      (boundedAboveFlatGlobalSectionEvaluation (Opposite.op X)) :=
  tensorEvaluation_unit f r

example (X : Scheme.{u}ᵒᵖ) :
    IsExact (boundedAboveFlatGlobalSectionModelFunctor.obj X).obj.waldhausen.cof
      (boundedAboveFlatGlobalSectionModelFunctor.obj X).obj.waldhausen.weq
      (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).asSmall.cof
      (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).asSmall.weq (evaluationSmall X) :=
  evaluationSmall_exact X

example (X : Scheme.{u}ᵒᵖ) :
    evaluationSmall X ≅ (evaluationModel X).hom.toFunctor :=
  evaluationNormalizationIso X

example (X : Scheme.{u}ᵒᵖ) (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (evaluationSmall X) (boundedAboveFlatGlobalSectionUnit X r) (evaluationSmallUnit X
      r) :=
  evaluationSmall_unit X r

example (X : Scheme.{u}ᵒᵖ) (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (evaluationModel X).hom.toFunctor (boundedAboveFlatGlobalSectionUnit X r)
      (evaluationSmallUnit X r) :=
  evaluationModel_unit X r

example {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
    (F : C ⥤ D) (x : C) (y : D) (e : F.obj x ≅ y)
    (α : 𝟭 C ≅ 𝟭 C) (β : 𝟭 D ≅ 𝟭 D) (h : Preserves F α β) :
    Preserves (CategoryTheory.rebaseFunctor F x y e) α β :=
  rebase_preserves F x y e α β h

