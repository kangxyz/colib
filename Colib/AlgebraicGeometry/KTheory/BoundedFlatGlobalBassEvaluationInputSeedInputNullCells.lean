/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedInputNullParam
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputPositiveSupport
public import Colib.Topology.Prespectrum.ConeSquareMovingNullEvaluation
public import Colib.Topology.Prespectrum.ConeCompositionPieces
public import Colib.Topology.Prespectrum.RelativeHomotopyOperationEvaluation
public import Colib.Topology.Prespectrum.CarrierSquareDescentEvaluation
public import Colib.Topology.Path.EvaluationFactorExtraction
public import Colib.Topology.Path.AssociatorEvaluation

/-!
# Pointwise native evaluation of the exact original input null surface

Both carrier sheets evaluate to the original whole positive null square at the strict source
projection. Every scalar operation is the one used by the frozen original producer.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedInputNull
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedCarrier
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The actual native evaluator of the mixed two-tip carrier. -/
abbrev nativeEval := CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
  (ordinary g) (shifted g)

/-- The original strict source projection is retained before the whole null square. -/
abbrev input (n : ℕ)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :=
  (sectionMap (projection.app Y)).map n x

/-- The original intermediate moving-null square, before the prescribed boundary correction. -/
abbrev originalMoving :=
  coneSquareNullMovingSquare (InputPositive.strictChart Y)
    (GlobalRawBass.InputIdentityPositive.chart X)
    (InputPositive.source g) (InputPositive.target g)
    (evaluationComparison (polynomial.map g)) (evaluationComparison (laurent.map g))
    (InputPositive.square g)

/-- The unchanged native three-piece composition correction. -/
abbrev originalCorrection :=
  coneSquareCompositionNullComparison (InputPositive.strictChart Y)
    (GlobalRawBass.InputIdentityPositive.chart Y) (GlobalRawBass.InputIdentityPositive.chart X)
    (GlobalBassEvaluation.evaluation (polynomial.obj Y))
    (GlobalBassEvaluation.evaluation (laurent.obj Y))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (polynomial.map g))
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
    (evaluationComparison (plus.app Y)) (GlobalRawBass.plusSquareHomotopy g)

/-- Reanchoring changes the scalar sheet without changing any native Laurent value. -/
theorem sheet_native (e : Bool) (n : ℕ)
    (y : |nerve (Codiscrete (Node (laurentRef g)))|)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    nativeEval g n (sheet g e y) x =
      (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)).map n
        (pointwisePrespectrumFamily (laurentRef g) n y x) := by
  cases e
  · exact CutOpenCarrier.nativeEval_laurentInclusion _ _ _ _ _ n y x
  · change nativeEval g n
      (CutOpenCarrier.laurentInclusion _ _ _ _ _
        (mapParameter (ModelSimplex.reanchorNode (commonUnit g)) y)) x = _
    exact (CutOpenCarrier.nativeEval_laurentInclusion _ _ _ _ _ n
      (mapParameter (ModelSimplex.reanchorNode (commonUnit g)) y) x).trans
      (congrArg ((mappingConeInclusion (prespectrumMap (chart (X := X)))).map n)
        (pointwise_reanchor (commonUnit g) n y x))

/-- Both distinct cylinders preserve every original cone height and polynomial value. -/
theorem cylinder_native (e : Bool) (n : ℕ)
    (p : |nerve (Codiscrete (Node (polyRef g)))|) (s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    nativeEval g n (cylinder g e (p, s)) x =
      ReducedMappingCone.cylinder _ _
        ((GlobalRawBass.InputIdentityPositive.chart X).map n)
        (s, pointwisePrespectrumFamily (polyRef g) n p x) := by
  cases e
  · exact CutOpenCarrier.nativeEval_cylinderMinus _ _ _ _ _ n p s x
  · exact CutOpenCarrier.nativeEval_cylinderPlus _ _ _ _ _ n p s x

/-- The tips have their common native point while remaining distinct carrier points. -/
theorem tip_native (e : Bool) (n : ℕ)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    nativeEval g n (tip g e) x =
      (mappingCone (GlobalRawBass.InputIdentityPositive.chart X)).point n := by
  cases e
  · exact CutOpenCarrier.nativeEval_tipMinus _ _ _ _ _ n x
  · exact CutOpenCarrier.nativeEval_tipPlus _ _ _ _ _ n x

/-- The polynomial edge is the original input comparison after strict source projection. -/
theorem polynomial_native (n : ℕ) (r : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    pointwisePrespectrumFamily (polyRef g) n (polynomialEdge g r) x =
      (evaluationComparison (polynomial.map g)).level n (r, input n x) := by
  change pointwisePrespectrumFamily (polyRef g) n
    (CommonReferenceNerve.parameter _ _ (SimplexParameters.edge (k := 7) 0 3 r)) x = _
  rw [pointwisePrespectrumFamily_parameter]
  have h := InputCommutingParameter.native (polynomial.map g) (projection.app Y)
    (projection.app X) g (projection.naturality g) n r 0 x
  change prespectrumSimplexFamily _ n (InputCommutingParameter.parameter (r, 0), x) = _ at h
  rw [InputCommutingParameter.parameter_left] at h
  exact h.trans ((InputCommutingSquare.square (polynomial.map g) (projection.app Y)
    (projection.app X) g (projection.naturality g)).left n r x)

/-- Both original chart coordinates have exactly the selected whole positive native square. -/
theorem chart_native (e : Bool) (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    nativeEval g n (chartParameter g e (r, s)) x =
      (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)).map n
        ((InputPositive.square g).level n (r, (s, input n x))) := by
  change nativeEval g n (sheet g e (InputChartSquareParameter.plusParameter g (r, s))) x = _
  rw [sheet_native, pointwisePrespectrumFamily_eq_compact]
  exact congrArg ((mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)).map n)
    (DFunLike.congr_fun
      (InputChartSquareParameter.native g plus GlobalRawBass.plus_projection n) ((r, s), x))

/-- The two exact path-time cells recover the original moving-null square pointwise. -/
theorem moving_native (e : Bool) (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    nativeEval g n ((movingSquare g e).parameter (r, s)) x =
      (originalMoving g).level n (r, (s, input n x)) := by
  change nativeEval g n (((chartSwap g e).trans (cylinderSwap g e)) (s, r)) x = _
  rw [ContinuousMap.Homotopy.trans_apply, coneSquareNullMovingSquare_apply]
  split
  · exact chart_native g e n r _ x
  · change nativeEval g n (cylinder g e (polynomialEdge g r, _)) x = _
    rw [cylinder_native, polynomial_native]
    rfl

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedInputNull
