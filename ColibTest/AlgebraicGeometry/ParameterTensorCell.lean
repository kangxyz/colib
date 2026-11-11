/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorCell
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite MonoidalCategory
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
noncomputable section

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    tensorCellCylinder Q X 0 =
      (((stages 0).map (evaluationModel (op (scheme Q X))) ▷ Δ[1]) ▷ Δ[1]) ≫
        tensorUnitPullbackSmallCoefficientCylinder (coefficientMap Q X)
          (ParameterLaurentUnit.projectedLaurentScalar Q X) :=
  tensorCellCylinder_zero Q X

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (k : ℕ) :
    tensorCellCylinder Q X k =
      rowTransformationCylinder
        (F := tensorModelMap Q X) (G := tensorModelMap Q X)
        (whiskerLeft (evaluationModel (op (scheme Q X))).hom.toFunctor
          (tensorUnitPullbackModelTransformation (coefficientMap Q X)
            (ParameterLaurentUnit.projectedLaurentScalar Q X)))
        (fun A => tensorUnitPullbackModelTransformation_weak (coefficientMap Q X)
          (ParameterLaurentUnit.projectedLaurentScalar Q X)
          ((evaluationModel (op (scheme Q X))).hom.toFunctor.obj A)) k :=
  tensorCellCylinder_eq Q X k

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (k : ℕ) :
    tensorCellRealization Q X k =
      rowTransformationRealization (tensorModelUnit Q X) (tensorModelUnit_weak Q X) k :=
  tensorCellRealization_eq Q X k

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (k : ℕ) (t s : unitInterval)
    (x : stageSpace k ((ParameterModels.ambient Q).obj X)) :
    Path.toContinuousMap
      ((rowTransformationSpectrumHomotopy (tensorModelUnit Q X)
        (tensorModelUnit_weak Q X)).level (k + 1) (t, x)) s =
      tensorCellRealization Q X k (s, (t, x)) :=
  tensorCell_succ Q X k t s x

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (t a s : unitInterval)
    (γ : Path (stagePoint 0 ((ParameterModels.ambient Q).obj X))
      (stagePoint 0 ((ParameterModels.ambient Q).obj X))) :
    Path.toContinuousMap (Path.toContinuousMap
      ((rowTransformationSpectrumHomotopy (tensorModelUnit Q X)
        (tensorModelUnit_weak Q X)).level 0 (t, γ)) a) s =
      tensorCellRealization Q X 0 (s, (t, γ a)) :=
  tensorCell_zero Q X t a s γ

