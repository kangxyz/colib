/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedNaturality
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationEquivalence
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputNaturality
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputCompositionSpan
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedSquare

/-! Regression checks for the arbitrary-scheme Bass input endpoints, covering the original
mixed seed words and independent clocks. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace ColibTest.BoundedFlatGlobalBassEvaluationEndpoints
open GlobalBassEvaluation GlobalSectionChangeIndex CommonReferenceNerve
open Path.CarrierHalfPaths
variable {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)

example (T : Scheme.{u}) (n : ℕ) :
    Topology.IsWeakHomotopyEquivalence ((spanEvaluation T).map n) ∧
    Topology.IsWeakHomotopyEquivalence ((coneEvaluation T).map n) ∧
    Topology.IsWeakHomotopyEquivalence ((stepEvaluation T).map n) :=
  ⟨spanEvaluation_level_isWeakHomotopyEquivalence T n,
    coneEvaluation_level_isWeakHomotopyEquivalence T n,
    stepEvaluation_level_isWeakHomotopyEquivalence T n⟩

example (T : Scheme.{u}) :
    Topology.IsWeakHomotopyEquivalence ((spanEvaluation T).map 0) ∧
    Topology.IsWeakHomotopyEquivalence ((coneEvaluation T).map 0) ∧
    Topology.IsWeakHomotopyEquivalence ((stepEvaluation T).map 0) ∧
    IsStableEquivalence (stepEvaluation T) :=
  ⟨spanEvaluation_level_isWeakHomotopyEquivalence T 0,
    coneEvaluation_level_isWeakHomotopyEquivalence T 0,
    stepEvaluation_level_isWeakHomotopyEquivalence T 0, stepEvaluation_isStableEquivalence T⟩

example : Homotopy
    ((((KTheory.Bass.strictDiagramFunctor squareFunctor).obj
      sectionDiagram).map g.op) ≫ stepEvaluation X)
    (stepEvaluation Y ≫ GlobalRawBass.map g) :=
  InputNaturality.stepHomotopy g

example (T : Scheme.{u}) : (GlobalRawBass.transitionInputHomotopy (𝟙 T)).Square
    (coneSquareIdentityTrack (GlobalRawBass.transition T))
    (Homotopy.precomp (GlobalRawBass.transition T) (GlobalRawBass.InputIdentity.mapHomotopy T))
    ((boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy T).postcomp (GlobalRawBass.transition T)) :=
  GlobalRawBass.InputIdentitySeedSquare.square T

example : Homotopy (GlobalRawBass.spanMap (g ≫ h))
    (GlobalRawBass.spanMap h ≫ GlobalRawBass.spanMap g) :=
  GlobalRawBass.InputCompositionSpan.homotopy g h

/-- The whole common A word agrees before native evaluation at every seed time. -/
theorem a_word (s : unitInterval) : InputSeedStrictFace.parameter g (0, s) =
    InputSeedInputFace.parameter g (0, s) := InputSeedSourceSeam.face g s

/-- The whole common B word agrees before native evaluation at every seed time. -/
theorem b_word (s : unitInterval) : InputSeedPostFace.parameter g (0, s) =
    InputSeedInputFace.parameter g (1, s) := InputSeedPostSourceSeam.face g s

/-- The whole common C word agrees before native evaluation at every seed time. -/
theorem c_word (s : unitInterval) : InputSeedPostFace.parameter g (1, s) =
    InputSeedTransitionFace.parameter g (0, s) := InputSeedPostTargetSeam.face g s

/-- The whole common D word agrees before native evaluation at every seed time. -/
theorem d_word (s : unitInterval) : InputSeedStrictFace.parameter g (1, s) =
    InputSeedEvalFace.parameter g (0, s) := InputSeedStrictTargetSeam.face g s

/-- The whole common E word agrees before native evaluation at every seed time. -/
theorem e_word (s : unitInterval) : InputSeedTransitionFace.parameter g (1, s) =
    InputSeedEvalFace.parameter g (1, s) := InputSeedRawTargetSeam.face g s

/-- The entire prescribed long route retains its original concatenation clocks. -/
theorem long_route (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
        (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g)
        n (InputSeedRoutes.longParameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.longRoute g).level n (r, x)) s :=
  InputSeedRoutes.long_native g n r s x

/-- The actual assembled carrier retains the original middle and final quarter clocks. -/
theorem original_quarters (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
        (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g)
        n (InputSeedRoutes.longParameter g (upper (lower r), s)) x) =
      (GlobalRawBass.coneMap g).map n ((conjugation Y).level n (r, (s, x))) ∧
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
        (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g)
        n (InputSeedRoutes.longParameter g (upper (upper r), s)) x) =
      (GlobalRawBass.InputSeed.conjugateComparison g).level n
        (r, (s, (GlobalBassEvaluation.evaluation Y).map n x)) :=
  ⟨(InputSeedRoutes.long_native g n (upper (lower r)) s x).trans
      (InputSeedWords.long_second g n r s x),
    (InputSeedRoutes.long_native g n (upper (upper r)) s x).trans
      (InputSeedWords.long_third g n r s x)⟩

/-- The two complete original native routes admit the actual relative comparison. -/
def originalComparison :
    (InputSeedWords.longRoute g).RelHomotopy (InputSeedWords.shortRoute g) :=
  InputSeedNaturality.comparison g

/-- Both selected whole faces survive the relative comparison literally. -/
theorem original_faces (n : ℕ) (s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    (originalComparison g).level n (0, (s, x)) =
      (InputSeedWords.longRoute g).level n (s, x) ∧
    (originalComparison g).level n (1, (s, x)) =
      (InputSeedWords.shortRoute g).level n (s, x) :=
  ⟨((originalComparison g).level n).apply_zero (s, x),
    ((originalComparison g).level n).apply_one (s, x)⟩

/-- Every comparison slice fixes both original seed-input endpoint maps. -/
theorem fixed_endpoint_maps (n : ℕ) (r : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    (originalComparison g).level n (r, (0, x)) =
      (strictSeed Y ≫ (InputSeedWords.strictInput g ≫ stepEvaluation X)).map n x ∧
    (originalComparison g).level n (r, (1, x)) =
      (GlobalBassEvaluation.evaluation Y ≫
        (boundedAboveFlatPerfectPullbackPrespectrumMap g ≫ GlobalRawBass.transition X)).map n x :=
  ⟨((originalComparison g).at r).at_zero n x, ((originalComparison g).at r).at_one n x⟩

/-- The full based line is fixed independently of comparison and route time. -/
theorem based_line (n : ℕ) (r s : unitInterval) :
    (originalComparison g).level n
      (r, (s, (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).point n)) =
      (GlobalRawBass.step X).point n :=
  ((originalComparison g).at r).at_point n s

/-- All independent comparison, route and loop times recover the actual finite extension. -/
theorem extension_value (n : ℕ) (r s t : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    Path.toContinuousMap ((originalComparison g).level n (r, (s, x))) t =
      (GlobalRawBass.InputIdentityPositive.inclusion X).map n
        (CutOpenCarrier.nativeEval (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
          (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g)
          n ((InputSeedRoutes.surfaces g).boundary.carrier ((r, s), t)) x) :=
  InputSeedNaturality.comparison_apply g n r s t x

/-- The original structure coordinate stays independent of all three other times. -/
theorem independent_structure (n : ℕ) (r s t v : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    Path.toContinuousMap ((originalComparison g).level (n + 1)
      (r, (s, (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).structureMap
        n x t))) v =
    Path.toContinuousMap ((GlobalRawBass.step X).structureMap n
      ((originalComparison g).level n (r, (s, x))) t) v :=
  congrArg (fun p ↦ Path.toContinuousMap p v) ((originalComparison g).comm n r s x t)

/-- The two carrier tips remain distinct, including after assembling both entire routes. -/
theorem distinct_tips :
    CutOpenCarrier.tipMinus (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
      (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g) ≠
    CutOpenCarrier.tipPlus (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
      (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g) :=
  InputSeedCarrier.tips_distinct g

/-- Neither moving evaluation time identifies the ordinary and shifted whole seed edges. -/
theorem moving_tips_distinct (r s : unitInterval) :
    InputSeedEvalFace.parameter g (r, 0) ≠ InputSeedEvalFace.parameter g (s, 1) := by
  rw [InputSeedEvalFace.zero, InputSeedEvalFace.one]
  exact InputSeedCarrier.tips_distinct g

end ColibTest.BoundedFlatGlobalBassEvaluationEndpoints
