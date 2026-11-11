/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorReturnedCell
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
noncomputable section

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (A : ((ParameterModels.ambient Q).obj X).obj.Obj) :
    (boundedAboveFlatGlobalSectionModelFunctor.obj (op (scheme Q (laurent.op.obj
      X)))).obj.waldhausen.weq
      ((returnedTensorUnit Q X).app A) :=
  returnedTensorUnit_weak Q X A

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    ((initialCell Q X).trans (returnedMovement Q X)).RelHomotopy
      ((returnedMovement Q X).trans (returnedTensorCell Q X)) :=
  returnedPasting Q X

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (t : unitInterval) :
    (returnedTensorCell Q X).at t =
      (rowTransformationSpectrumHomotopy (tensorModelUnit Q X)
        (tensorModelUnit_weak Q X)).at t ≫
        rowLoopMap (evaluationInverseModel (op (scheme Q (laurent.op.obj X)))) :=
  returnedTensorCell_at Q X t

