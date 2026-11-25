/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputCube
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputConeSource
public import Colib.Topology.Prespectrum.ConeSquareMapMovingCoherence
public import Colib.Topology.Prespectrum.ParameterLoopingHomotopy
public import Colib.Util.References

/-!
# Whole one-step input naturality of the original global Bass evaluation

The fully constructed mixed comparison cube yields the original cone and parameter-looped
input homotopies. The Laurent inclusion moves through the actual evaluation comparison and
the original nested cone heights are retained. This is an arrowwise homotopy, with no strict
raw functor or higher-stage coherence asserted.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputNaturality
open GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The constructed comparison square supplies the whole original direct-to-composite cone law. -/
def directConeHomotopy : Homotopy (InputConeSource.directConeMap g)
    (coneEvaluation Y ≫ GlobalRawBass.coneMap g) :=
  coneSquareCompositionHomotopyOfSquare
    (StrictSquare.comparison (sectionSquare Y))
    (GlobalRawBass.comparison Y) (GlobalRawBass.comparison X)
    (spanEvaluation Y) (evaluation (laurent.obj Y))
    (GlobalRawBass.spanMap g) (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))
    (comparisonHomotopy Y) (GlobalRawBass.inputComparisonHomotopy g)
    (InputComparisonTracks.source g) (inputSpanHomotopy g)
    (evaluationComparison (laurent.map g)) (InputCube.square g)

/-- The whole original strict cone-input composite is compared to the independent raw composite. -/
def coneHomotopy : Homotopy (InputConeSource.strictConeMap g ≫ coneEvaluation X)
    (coneEvaluation Y ≫ GlobalRawBass.coneMap g) :=
  (directConeHomotopy g).cast (InputConeSource.strict_comp_evaluation g).symm rfl

/-- The original strict Bass diagram has precisely the parameter-looped strict cone input. -/
theorem strict_input_eq :
    (((KTheory.Bass.strictDiagramFunctor squareFunctor).obj
      sectionDiagram).map g.op) =
      parameterLoopingMap (InputConeSource.strictConeMap g) := InputConeSource.strict_input_eq g

/-- The actual one-step evaluation is input-natural through the constructed whole raw homotopy. -/
@[colib_tag "COL-1342"]
def stepHomotopy : Homotopy
    ((((KTheory.Bass.strictDiagramFunctor squareFunctor).obj
      sectionDiagram).map g.op) ≫ stepEvaluation X)
    (stepEvaluation Y ≫ GlobalRawBass.map g) :=
  (coneHomotopy g).parameterLooping.cast
    (parameterLoopingFunctor.map_comp (InputConeSource.strictConeMap g) (coneEvaluation X))
    (parameterLoopingFunctor.map_comp (coneEvaluation Y) (GlobalRawBass.coneMap g))

/-- The whole cone inclusion keeps the actual unpaused Laurent evaluation comparison. -/
theorem coneHomotopy_inclusion (n : ℕ) (r : unitInterval)
    (x : (sectionDiagram.obj (op (laurent.obj Y))).space n) :
    (coneHomotopy g).level n
      (r, (mappingConeInclusion (StrictSquare.comparison (sectionSquare Y))).map n x) =
      (mappingConeInclusion (GlobalRawBass.comparison X)).map n
        ((evaluationComparison (laurent.map g)).level n (r, x)) := rfl

/-- The actual whole cone homotopy yields its two prescribed original cylinder faces exactly. -/
def originalNullSquare : MappingConeMapNullSquare
    (StrictSquare.comparison (sectionSquare Y))
    (Homotopy.precomp (mappingConeInclusion (StrictSquare.comparison (sectionSquare Y)))
      (coneHomotopy g)) :=
  mappingConeNullSquareOfHomotopy (StrictSquare.comparison (sectionSquare Y))
    (Homotopy.precomp (mappingConeInclusion (StrictSquare.comparison (sectionSquare Y)))
      (coneHomotopy g)) (coneHomotopy g) (fun _ _ _ => rfl)

/-- The derived original null square retains its exact actual cone-cylinder values. -/
theorem originalNullSquare_level (n : ℕ) (q s : unitInterval)
    (x : (StrictSquare.span (sectionSquare Y)).space n) :
    (originalNullSquare g).level n (q, (s, x)) =
      (coneHomotopy g).level n
        (q, (mappingConeHomotopy (StrictSquare.comparison (sectionSquare Y))).level n (s, x)) :=
  rfl

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputNaturality
