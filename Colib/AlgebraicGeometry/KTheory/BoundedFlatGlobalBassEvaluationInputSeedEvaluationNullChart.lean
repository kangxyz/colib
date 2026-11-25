/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvaluationNullCone
public import Colib.Topology.Path.RetypedConeNullComparison
public import Colib.Topology.Path.EvaluationFactorExtraction

/-!
# Both whole original evaluation-chart surfaces in the objectwise carrier

The five original positive nodes occupy their proved face of the common chart simplex.
The selected geometric pasting, source equality transport, and binary normalization clock
are unchanged. Each polynomial rail meets its actual cylinder before native evaluation.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite Topology
  Convexity Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationNullChart
open CommonReferenceNerve InputSeedEvaluationCarrier
variable (X : Scheme.{u})

/-- The original chart simplex on its ordinary or complete unit-shifted Laurent sheet. -/
def sheetMap (e : Bool) : C(StdSimplex ℝ (Fin 8), Carrier X) :=
  (CutOpenCarrier.laurentInclusion (polyRef X) (chart X) (laurentRef X)
    (ordinary X) (shifted X)).comp
      (if e then (mapParameter (ModelSimplex.reanchorNode (commonUnit X))).comp
        (parameter (laurentRef X) (InputChartSimplex.nodes X))
      else parameter (laurentRef X) (InputChartSimplex.nodes X))

/-- The complete original simplex family is retained on each separately anchored sheet. -/
theorem sheetMap_native (e : Bool) (n : ℕ) (z : StdSimplex ℝ (Fin 8))
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (sheetMap X e z) x =
      (mappingConeInclusion (GlobalRawBass.InputIdentityPositive.chart X)).map n
        (prespectrumSimplexFamily (InputChartSimplex.simplex X) n (z, x)) := by
  cases e
  · change CutOpenCarrier.nativeEval _ _ _ _ _ n
      (CutOpenCarrier.laurentInclusion _ _ _ _ _ (parameter _ _ z)) x = _
    rw [CutOpenCarrier.nativeEval_laurentInclusion,
      pointwisePrespectrumFamily_parameter]
    rfl
  · change CutOpenCarrier.nativeEval _ _ _ _ _ n
      (CutOpenCarrier.laurentInclusion _ _ _ _ _
        (mapParameter (ModelSimplex.reanchorNode (commonUnit X)) (parameter _ _ z))) x = _
    rw [CutOpenCarrier.nativeEval_laurentInclusion, pointwise_reanchor,
      pointwisePrespectrumFamily_parameter]
    rfl

/-- The original chart evaluation edge. -/
abbrev positiveMovement (e : Bool) :=
  (edge (k := 7) 0 3).map (sheetMap X e).continuous

/-- The original polynomial evaluation edge after its actual raw chart. -/
abbrev polynomialMovement (e : Bool) :=
  (edge (k := 7) 3 4).map (sheetMap X e).continuous

/-- The original Laurent evaluation edge, with its original reference transport. -/
abbrev laurentMovement (e : Bool) :=
  (edge (k := 7) 0 1).map (sheetMap X e).continuous

/-- Both actual raw positive normalization pieces retain their original half-clock. -/
abbrev newPositive (e : Bool) :=
  ((edge (k := 7) 1 2).trans (edge (k := 7) 2 4)).map (sheetMap X e).continuous

/-- The entire originally chosen positive chart pasting on the selected sheet. -/
def positivePasting (e : Bool) :
    ((positiveMovement X e).trans (polynomialMovement X e)).Homotopy
      ((laurentMovement X e).trans (newPositive X e)) :=
  ((InputParameter.chart InputChartSimplex.plusFace).map (sheetMap X e)).cast
    (by simp only [Path.map_trans]; rfl)
    (by simp only [Path.map_trans]; rfl)

/-- Both original chart-pasting coordinates survive source transport and native evaluation. -/
theorem positivePasting_native (e : Bool) (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (positivePasting X e (r, s)) x =
      (InputPositiveNull.positivePasting X).level n (r, (s, x)) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (sheetMap X e (InputParameter.chart InputChartSimplex.plusFace (r, s))) x = _
  rw [sheetMap_native, InputChartSimplex.plus_native]
  rfl

/-- Each complete polynomial edge attaches to its own sheet at every original movement time. -/
theorem polynomial_seam (e : Bool) (t : I) :
    polynomialMovement X e t = (InputSeedEvaluationNullCone.square X e).parameter (t, 0) := by
  cases e
  · change CutOpenCarrier.laurentInclusion _ _ _ _ _
      (parameter _ _ (edge (k := 7) 3 4 t)) =
        CutOpenCarrier.cylinderMinus _ _ _ _ _ (movement X t, 0)
    rw [CutOpenCarrier.cylinderMinus_zero, movement_attach]
  · change CutOpenCarrier.laurentInclusion _ _ _ _ _
      (mapParameter (ModelSimplex.reanchorNode (commonUnit X))
        (parameter _ _ (edge (k := 7) 3 4 t))) =
        CutOpenCarrier.cylinderPlus _ _ _ _ _ (movement X t, 0)
    rw [CutOpenCarrier.cylinderPlus_zero, shifted_movement_attach]

/-- The old native cone path, retyped only by the proved whole polynomial seam. -/
abbrev oldCone (e : Bool) := (InputSeedEvaluationNullCone.square X e).rebaseOld
  (polynomialMovement X e) (polynomial_seam X e)

/-- The new native cone path ends at the same selected sheet's distinct tip. -/
abbrev newCone (e : Bool) := (InputSeedEvaluationNullCone.square X e).rebaseNew
  (polynomialMovement X e) (polynomial_seam X e)

/-- The entire original cone boundary collapse followed by terminal-pause cancellation. -/
def coneComparison (e : Bool) : (oldCone X e).Homotopy
    ((polynomialMovement X e).trans (newCone X e)) :=
  ((InputSeedEvaluationNullCone.square X e).rebaseMovement
    (polynomialMovement X e) (polynomial_seam X e)).coneBoundary

/-- The exact cone-pasting surface retains both original parameters after endpoint retyping. -/
theorem coneComparison_native (e : Bool) (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (coneComparison X e (r, s)) x =
      (InputPositiveNull.conePasting X).level n (r, (s, x)) := by
  have h := (InputSeedEvaluationNullCone.square X e).rebaseMovement_coneBoundary_apply
    (polynomialMovement X e) (polynomial_seam X e) r s
  change coneComparison X e (r, s) = InputSeedEvaluationNullCone.boundary X e (r, s) at h
  rw [h]
  exact InputSeedEvaluationNullCone.boundary_conePasting X e n r s x

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationNullChart
