/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputDescNative
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCompactAttachment

/-!
# Both whole selected descent surfaces in the mixed input reference

The original Y descent surface after raw Laurent pullback and the original X descent surface
after strict input pullback have compact parameters in one actual common-reference nerve.
Their complete two-dimensional families, including the selected constant-path insertions,
are preserved. This does not identify the additional mixed cone boundary faces or fill them.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputMixedDesc
open GlobalSectionChangeIndex

/-- The exact compact nerve parameter of the already selected original descent surface. -/
def descParameter (X : Scheme.{u}) :=
  (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X) (InputChartSimplex.nodes X)).comp
    InputChartSimplex.descParameter.toContinuousMap

/-- Every point retains the entire original descent family and all selected half clocks. -/
theorem desc_parameter_native (X : Scheme.{u}) (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputChartSimplex.sourceMap X)
      (descParameter X) n ((r, s), x) = (descPasting X).level n (r, (s, x)) := by
  exact (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ (descParameter X)
    (InputChartSimplex.nodes X) (r, s) (InputChartSimplex.descParameter (r, s)) rfl n x).trans
      (InputChartSimplex.desc_native X n r s x)

/-- The same scalar surface descends through the original three-side parameter quotient. -/
def descSquareParameter (X : Scheme.{u}) :=
  (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X) (InputChartSimplex.nodes X)).comp
    (CategoryTheory.Waldhausen.IteratedS.SimplexParameters.collapsed
      InputChartSimplex.descParameter)

/-- The entire original moving square, including its quotient-collapse clock, is recovered. -/
theorem desc_square_parameter_native (X : Scheme.{u}) (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputChartSimplex.sourceMap X)
      (descSquareParameter X) n ((r, s), x) = (descPasting X).toSquare.level n (r, (s, x)) := by
  exact (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ (descSquareParameter X)
    (InputChartSimplex.nodes X) (r, s)
    (CategoryTheory.Waldhausen.IteratedS.SimplexParameters.collapsed
      InputChartSimplex.descParameter (r, s)) rfl n x).trans
    (CategoryTheory.Waldhausen.IteratedS.SimplexParameters.HomotopyLift.toSquare
      (InputChartSimplex.simplex X) (InputChartSimplex.desc_native X) n r s x)

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The mixed reference is the original strict total Laurent pullback followed by evaluation. -/
def sourceMap :=
  boundedAboveFlatGlobalSectionModelFunctor.map
    ((laurent.map g) ≫ GlobalRawBass.laurentProjection.app Y).op ≫
    evaluationModel (op (laurent.obj X))

/-- The postcomposed Y surface keeps the original first evaluation comparison as reference. -/
def postSourceIso : (sourceMap g).hom.toFunctor ≅
    (InputChartSimplex.sourceMap Y ≫ evaluationRawMap (laurent.map g)).hom.toFunctor :=
  evaluationCompositionFirstIso (laurent.map g) (GlobalRawBass.laurentProjection.app Y)

/-- Every original Y node is postcomposed and anchored with its full specified comparison. -/
def postNode := CommonReferenceNerve.attachPostcompNode (InputChartSimplex.sourceMap Y)
  (evaluationRawMap (laurent.map g)) (sourceMap g) (postSourceIso g)

/-- The whole selected Y descent surface in the mixed common reference. -/
def postParameter :=
  (CommonReferenceNerve.mapParameter (postNode g)).comp (descParameter Y)

/-- The X reference retains the actual Laurent square and strict composition transport. -/
def preSourceIso : (sourceMap g).hom.toFunctor ≅
    (boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫
      InputChartSimplex.sourceMap X).hom.toFunctor :=
  eqToIso (congrArg (fun k : laurent.obj X ⟶ Y =>
    (boundedAboveFlatGlobalSectionModelFunctor.map k.op ≫
      evaluationModel (op (laurent.obj X))).hom.toFunctor)
      (GlobalRawBass.laurentProjection.naturality g)) ≪≫
  eqToIso (congrArg (fun S => S ⋙ (evaluationModel (op (laurent.obj X))).hom.toFunctor)
    (congrArg (fun a => a.hom.toFunctor)
      (boundedAboveFlatGlobalSectionModelFunctor.map_comp
        g.op (GlobalRawBass.laurentProjection.app X).op))) ≪≫
  Functor.associator (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor
    (boundedAboveFlatGlobalSectionModelFunctor.map
      (GlobalRawBass.laurentProjection.app X).op).hom.toFunctor
      (evaluationModel (op (laurent.obj X))).hom.toFunctor

/-- Every original X node is strictly precomposed with its full original reference. -/
def preNode := CommonReferenceNerve.attachPrecompNode (InputChartSimplex.sourceMap X)
  (boundedAboveFlatGlobalSectionModelFunctor.map g.op) (sourceMap g) (preSourceIso g)

/-- The whole selected X descent surface in the same mixed common reference. -/
def preParameter :=
  (CommonReferenceNerve.mapParameter (preNode g)).comp (descParameter X)

/-- The Y face is the original whole descent surface after the actual raw Laurent map. -/
theorem post_parameter_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (sourceMap g) (postParameter g)
      n ((r, s), x) =
    (prespectrumMap (evaluationRawMap (laurent.map g))).map n
      ((descPasting Y).level n (r, (s, x))) := by
  change CommonReferenceNerve.compactPrespectrumFamily (sourceMap g)
    ((CommonReferenceNerve.mapParameter (CommonReferenceNerve.attachPostcompNode
      (InputChartSimplex.sourceMap Y) (evaluationRawMap (laurent.map g))
      (sourceMap g) (postSourceIso g))).comp (descParameter Y)) n ((r, s), x) = _
  rw [CommonReferenceNerve.compactPrespectrumFamily_attachPostcomp]
  exact congrArg ((prespectrumMap (evaluationRawMap (laurent.map g))).map n)
    (desc_parameter_native Y n r s x)

/-- The X face is the original whole descent surface after the actual strict input map. -/
theorem pre_parameter_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (sourceMap g) (preParameter g)
      n ((r, s), x) =
    (descPasting X).level n
      (r, (s, (prespectrumMap (boundedAboveFlatGlobalSectionModelFunctor.map g.op)).map n x)) := by
  change CommonReferenceNerve.compactPrespectrumFamily (sourceMap g)
    ((CommonReferenceNerve.mapParameter (CommonReferenceNerve.attachPrecompNode
      (InputChartSimplex.sourceMap X) (boundedAboveFlatGlobalSectionModelFunctor.map g.op)
      (sourceMap g) (preSourceIso g))).comp (descParameter X)) n ((r, s), x) = _
  rw [CommonReferenceNerve.compactPrespectrumFamily_attachPrecomp]
  exact desc_parameter_native X n r s _

/-- The whole selected Y moving square retains the actual quotient before postcomposition. -/
def postSquareParameter :=
  (CommonReferenceNerve.mapParameter (postNode g)).comp (descSquareParameter Y)

/-- The whole selected X moving square keeps the actual three-side quotient after precomposition. -/
def preSquareParameter :=
  (CommonReferenceNerve.mapParameter (preNode g)).comp (descSquareParameter X)

/-- Every point of the prescribed Y `toSquare` face survives the actual raw Laurent postmap. -/
theorem post_square_parameter_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (sourceMap g) (postSquareParameter g)
      n ((r, s), x) =
    (prespectrumMap (evaluationRawMap (laurent.map g))).map n
      ((descPasting Y).toSquare.level n (r, (s, x))) := by
  change CommonReferenceNerve.compactPrespectrumFamily (sourceMap g)
    ((CommonReferenceNerve.mapParameter (CommonReferenceNerve.attachPostcompNode
      (InputChartSimplex.sourceMap Y) (evaluationRawMap (laurent.map g))
      (sourceMap g) (postSourceIso g))).comp (descSquareParameter Y)) n ((r, s), x) = _
  rw [CommonReferenceNerve.compactPrespectrumFamily_attachPostcomp]
  exact congrArg ((prespectrumMap (evaluationRawMap (laurent.map g))).map n)
    (desc_square_parameter_native Y n r s x)

/-- Every point of the prescribed X `toSquare` face survives the actual strict input premap. -/
theorem pre_square_parameter_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (sourceMap g) (preSquareParameter g)
      n ((r, s), x) =
    (descPasting X).toSquare.level n
      (r, (s, (prespectrumMap (boundedAboveFlatGlobalSectionModelFunctor.map g.op)).map n x)) := by
  change CommonReferenceNerve.compactPrespectrumFamily (sourceMap g)
    ((CommonReferenceNerve.mapParameter (CommonReferenceNerve.attachPrecompNode
      (InputChartSimplex.sourceMap X) (boundedAboveFlatGlobalSectionModelFunctor.map g.op)
      (sourceMap g) (preSourceIso g))).comp (descSquareParameter X)) n ((r, s), x) = _
  rw [CommonReferenceNerve.compactPrespectrumFamily_attachPrecomp]
  exact desc_square_parameter_native X n r s _

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputMixedDesc
