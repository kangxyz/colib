/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorModelUnit
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
noncomputable section

example {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (K : (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory) :
    (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom.app K =
      (boundedAboveFlatPerfectGlobalUnitIso X r).hom.app
        ((boundedAboveFlatPerfectTensorUnitPullback f).obj K) :=
  tensorAutomorphism_scalar f r K

example {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    tensorUnitPullbackModelTransformation f r =
      (onFunctor (tensorUnitPullbackModelMap f).hom.toFunctor
        (evaluationSmallUnit (op X) r)).hom :=
  tensorModelTransformation_scalar f r

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    whiskerRight
      (onFunctor (boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q
      X).op).hom.toFunctor
        (boundedAboveFlatGlobalSectionUnit (op (scheme Q (laurent.op.obj X)))
          (ParameterLaurentUnit.projectedLaurentScalar Q X))).hom
      (evaluationModel (op (scheme Q (laurent.op.obj X)))).hom.toFunctor ≫
      (internalTensorModelIso Q X).hom =
    (internalTensorModelIso Q X).hom ≫
      whiskerLeft (evaluationModel (op (scheme Q X))).hom.toFunctor
        (tensorUnitPullbackModelTransformation (coefficientMap Q X)
          (ParameterLaurentUnit.projectedLaurentScalar Q X)) :=
  internalTensorModelIso_unit Q X

