/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorRowPasting
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
noncomputable section

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (A : ((ParameterModels.ambient Q).obj X).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (scheme Q (laurent.op.obj
      X)).toRingedSpace)).obj.waldhausen.weq
      ((internalModelUnit Q X).app A) :=
  internalModelUnit_weak Q X A

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (A : ((ParameterModels.ambient Q).obj X).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (scheme Q (laurent.op.obj
      X)).toRingedSpace)).obj.waldhausen.weq
      ((tensorModelUnit Q X).app A) :=
  tensorModelUnit_weak Q X A

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    tensorRowPasting Q X =
      rowTransformationPasting
        (F := internalModelMap Q X) (G := internalModelMap Q X)
        (G' := tensorModelMap Q X) (H := tensorModelMap Q X)
        (internalModelUnit Q X) (internalTensorModelIso Q X).hom
        (internalTensorModelIso Q X).hom (tensorModelUnit Q X)
        (internalModelUnit_weak Q X)
        (fun _ => (asSmallCategory (boundedAboveFlatPerfectWaldhausen
          (scheme Q (laurent.op.obj X)).toRingedSpace)).obj.waldhausen.weq_iso _ inferInstance)
        (fun _ => (asSmallCategory (boundedAboveFlatPerfectWaldhausen
          (scheme Q (laurent.op.obj X)).toRingedSpace)).obj.waldhausen.weq_iso _ inferInstance)
        (tensorModelUnit_weak Q X) (internalTensorModelIso_unit Q X) := rfl
