/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorReturnedStrictification

open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open KTheory.Bass KTheory.Bass.GeometricSquareInterchange
open AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
noncomputable section
universe u w

example (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    strictifiedIteratedCell Q i X =
      SchemeModelRowSeed.cell (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) i X :=
  strictifiedIteratedCell_eq Q i X

example (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    strictifiedNormalizedForward Q i X =
      SchemeModelRowSeed.normalizedBoundary (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) i X :=
  strictifiedNormalizedForward_eq Q i X

example (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    strictifiedIteratedCell Q i X =
      SchemeModelRowStrictification.iteratedCell (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
        (returnedTensorModel Q) (returnedTensorIso Q) (returnedTensorUnit Q)
        (returnedTensorIso_unit Q) i X := rfl

example (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    strictifiedNormalizedForward Q i X =
      SchemeModelRowStrictification.normalizedForward (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
        (returnedTensorModel Q) (returnedTensorIso Q) (returnedTensorUnit Q)
        (returnedTensorIso_unit Q) i X := rfl

variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})

example :
    projectionMap F ≫ plusMap F = projectionMap F ≫ minusMap F :=
  chartMap_projection F

example :
    (geometricSquare F).left.hom ≫ (geometricSquare F).hom.right =
      Functor.whiskerRight (NatTrans.op
        (baseProductProjection (laurentProjection (.of (ULift.{u} ℤ))))) F :=
  geometricSquare_diagonal F

