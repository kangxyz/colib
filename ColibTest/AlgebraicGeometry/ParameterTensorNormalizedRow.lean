/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorEvaluationRow

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

example {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory ⥤
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  tensorUnitPullbackNormalizedFunctor f

example {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    (tensorUnitPullbackFirstRowNormalizedAutomorphism f r).hom =
      whiskerRight (normalizedWeakTransformation (boundedAboveFlatPerfectTensorUnitPullback_exact f)
        (boundedAboveFlatPerfectTensorUnitPullback_exact f)
        (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom)
        (oneEmbedding (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)) :=
  tensorUnitPullbackFirstRowNormalizedAutomorphism_hom f r

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    scheme Q (laurent.op.obj X) ⟶ scheme Q X := coefficientMap Q X

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    ((ParameterModels.ambient Q).obj X).obj.Obj ⥤
      (boundedAboveFlatPerfectComplex (scheme Q X).toRingedSpace).FullSubcategory := evaluation Q X

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    firstRow Q X ≅ evaluation Q X ⋙
      tensorUnitPullbackNormalizedFunctor (coefficientMap Q X) ⋙
        oneEmbedding (boundedAboveFlatPerfectWaldhausen
          (scheme Q (laurent.op.obj X)).toRingedSpace) := firstRowNormalization Q X

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) {k n m : SimplexCategory}
    (A : Grid₂ n m ⥤ ((ParameterModels.ambient Q).obj X).obj.Obj)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    tensorUnitPullbackNormalizedCoefficientPrism (coefficientMap Q X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X) (A ⋙ evaluation Q X) τ θ =
      nerveCylinderDiagram (whiskerLeft (A ⋙ evaluation Q X)
        (normalizedWeakTransformation
          (boundedAboveFlatPerfectTensorUnitPullback_exact (coefficientMap Q X))
          (boundedAboveFlatPerfectTensorUnitPullback_exact (coefficientMap Q X))
          (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism (coefficientMap Q X)
            (ParameterLaurentUnit.projectedLaurentScalar Q X)).hom)) τ ⋙
        suspensionRow (boundedAboveFlatPerfectWaldhausen
          (scheme Q (laurent.op.obj X)).toRingedSpace) θ := prism Q X A τ θ
