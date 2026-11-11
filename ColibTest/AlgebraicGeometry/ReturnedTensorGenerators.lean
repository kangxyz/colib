/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatReturnedTensorGenerators
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ReturnedTensorConeRecognition
open AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open ModelDiagramRowInterchange
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
noncomputable section

example (Q : Scheme.{u})
    {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((ParameterModels.ambient Q).obj X)).space n) :
    ((DiagramRowRefinement.diagram (ParameterModels.ambient Q ⋙ prespectrumFunctor)
      (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
      (initial_naturality (ParameterModels.ambient Q))).map (laurent.op.map g)).map n
        (((tensorFamily Q).val X).level n (r, x)) =
      ((tensorFamily Q).val Y).level n
        (r, (prespectrumMap ((ParameterModels.ambient Q).map g)).map n x) :=
  tensorFamily_naturality Q g n r x

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (((tensorFamily Q).val X).trans (returnedMovement Q X)).RelHomotopy
      ((returnedMovement Q X).trans (returnedTensorCell Q X)) :=
  tensorFamilyReturnedPasting Q X

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    StrictSquare.MapHomotopy.ConeGeneratorLaw (tensorSquare Q X) (tensorSquare Q X).cone :=
  tensorSquare_generators Q X

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (K : Homotopy _ _)
    (h : StrictSquare.MapHomotopy.ConeGeneratorLaw (tensorSquare Q X) K) :
    K = (tensorSquare Q X).cone :=
  tensorSquare_unique Q X K h

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (n : ℕ) (r t : unitInterval) (γ : Path _ _) :
    Path.toContinuousMap ((tensorSquare Q X).looped.level n (r, γ)) t =
      (tensorSquare Q X).cone.level n (r, γ t) :=
  tensorSquare_looped_apply Q X n r t γ

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    CategoryTheory.Waldhausen.KMap
      (boundedAboveFlatPerfectInclusion_isExact (scheme Q (laurent.op.obj X)).toRingedSpace) 1
      (tensorUnitCoefficientKOneClass (scheme Q (laurent.op.obj X))
        (ParameterLaurentUnit.projectedLaurentScalar Q X)) =
      perfectGlobalUnitKOneClass (scheme Q (laurent.op.obj X))
        (ParameterLaurentUnit.projectedLaurentScalar Q X)
        (rankOnePerfectComplex (scheme Q (laurent.op.obj X))) :=
  coefficient_class Q X

