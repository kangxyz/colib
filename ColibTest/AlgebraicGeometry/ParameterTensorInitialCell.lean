/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorInitialCell
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Functor.IdentityAutomorphism
open KTheory.Bass Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
noncomputable section

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    initialCell Q X = ((ParameterLaurentTrack.ambientTrack Q).homotopy X).postcomp
      (RowRefinement.comparison
        (prespectrum ((ParameterModels.ambient Q).obj (laurent.op.obj X)))
        (ModelDiagramRowInterchange.initial (ParameterModels.ambient Q) (laurent.op.obj X))
        (ModelDiagramRowInterchange.initial_point (ParameterModels.ambient Q) (laurent.op.obj X))
        (ModelDiagramRowInterchange.initial_structure
          (ParameterModels.ambient Q) (laurent.op.obj X))) :=
  initialCell_eq Q X

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (t : unitInterval) :
    (rowTransformationSpectrumHomotopy (internalModelUnit Q X)
      (internalModelUnit_weak Q X)).at t =
    (initialCell Q X).at t ≫
      rowLoopMap (evaluationModel (op (scheme Q (laurent.op.obj X)))) :=
  internalCell_evaluation_at Q X t

example {V W T : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (J : W ⟶ T) (t : unitInterval) :
    (rowTransformationSpectrumHomotopy (F := F ≫ J) (G := G ≫ J)
      (whiskerRight η J.hom.toFunctor) (fun A => J.hom.isExact.weak _ (hη A))).at t =
    (rowTransformationSpectrumHomotopy η hη).at t ≫ rowLoopMap J :=
  rowTransformationSpectrumHomotopy_postcomp_at η hη J t
