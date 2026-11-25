/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedSourceSeam
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedPostSourceSeam
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedPostTargetSeam
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedStrictTargetSeam
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCutOpenSurfaceBoundary
public import Colib.Topology.Path.ScalarRectangleConcatenation

/-!
# Both whole original mixed evaluation seed routes

The three-piece long route and two-piece short route use the actual five carrier faces and
proved whole-word seams. Their clocks remain literal half and quarter clocks. The two complete
outer faces and four fixed endpoint faces form a legitimate six-face carrier boundary.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum Topology.ScalarRectangle
open scoped Topology unitInterval
universe u v
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedRoutes
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedCarrier

private theorem concat_fixed {Z : Type v} [TopologicalSpace Z]
    (P Q : C(unitInterval × unitInterval, Z)) (h : ∀ t, P (1, t) = Q (0, t)) (t : unitInterval)
      (z : Z)
    (hP : ∀ r, P (r, t) = z) (hQ : ∀ r, Q (r, t) = z) (r : unitInterval) :
    concatFirst P Q h (r, t) = z := by
  change ((rowHomotopy P).trans ((rowHomotopy Q).cast
    (ContinuousMap.ext (fun s => (h s).symm)) rfl)) (r, t) = z
  rw [ContinuousMap.Homotopy.trans_apply]
  split
  · exact hP _
  · exact hQ _

private theorem concat_native {Z : Type v} [TopologicalSpace Z]
    (P Q : C(unitInterval × unitInterval, Z)) (h : ∀ t, P (1, t) = Q (0, t))
    {E F : Topology.LoopPrespectrum.{u}} {f g k : E ⟶ parameterLooping F}
    (H : Topology.LoopPrespectrum.Homotopy f g) (K : Topology.LoopPrespectrum.Homotopy g k)
    (n : ℕ) (x : E.space n)
    (ev : Z → F.space n)
    (hP : ∀ r s, ev (P (r, s)) = Path.toContinuousMap (H.level n (r, x)) s)
    (hQ : ∀ r s, ev (Q (r, s)) = Path.toContinuousMap (K.level n (r, x)) s)
    (r s : unitInterval) : ev (concatFirst P Q h (r, s)) =
      Path.toContinuousMap ((H.trans K).level n (r, x)) s := by
  change ev (((rowHomotopy P).trans ((rowHomotopy Q).cast
    (ContinuousMap.ext (fun t => (h t).symm)) rfl)) (r, s)) =
      Path.toContinuousMap (((H.levelHomotopy n).trans (K.levelHomotopy n)) (r, x)) s
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact hP _ s
  · exact hQ _ s

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The last two original long-route faces retain their literal comparison-time half cut. -/
def tailParameter : C(unitInterval × unitInterval, Carrier g) :=
  concatFirst (InputSeedPostFace.parameter g) (InputSeedTransitionFace.parameter g)
    (InputSeedPostTargetSeam.face g)

/-- The original first face meets that complete two-piece tail along its entire B word. -/
theorem tail_join (s : unitInterval) : InputSeedInputFace.parameter g (1, s) =
    tailParameter g (0, s) :=
  (InputSeedPostSourceSeam.face g s).symm.trans
    (concatFirst_zero (InputSeedPostFace.parameter g) (InputSeedTransitionFace.parameter g)
      (InputSeedPostTargetSeam.face g) s).symm

/-- The complete actual three-piece long route retains the original half and quarter cuts. -/
def longParameter : C(unitInterval × unitInterval, Carrier g) :=
  concatFirst (InputSeedInputFace.parameter g) (tailParameter g) (tail_join g)

/-- The complete actual short route retains both original faces and its original half cut. -/
def shortParameter : C(unitInterval × unitInterval, Carrier g) :=
  concatFirst (InputSeedStrictFace.parameter g) (InputSeedEvalFace.parameter g)
    (InputSeedStrictTargetSeam.face g)

/-- The whole left route begins at the unchanged common A word. -/
theorem long_source (s : unitInterval) : longParameter g (0, s) =
    InputSeedStrictFace.sourceParameter g s :=
  (concatFirst_zero (InputSeedInputFace.parameter g) (tailParameter g) (tail_join g) s).trans
    ((InputSeedSourceSeam.face g s).symm.trans (InputSeedStrictFace.source g s))

/-- The whole left route ends at the unchanged common E word. -/
theorem long_target (s : unitInterval) : longParameter g (1, s) =
    InputSeedTransitionFace.targetParameter g s :=
  (concatFirst_one (InputSeedInputFace.parameter g) (tailParameter g) (tail_join g) s).trans
    ((concatFirst_one (InputSeedPostFace.parameter g) (InputSeedTransitionFace.parameter g)
      (InputSeedPostTargetSeam.face g) s).trans (InputSeedTransitionFace.target g s))

/-- The whole right route begins at precisely the same original A word. -/
theorem short_source (s : unitInterval) : shortParameter g (0, s) =
    InputSeedStrictFace.sourceParameter g s :=
  (concatFirst_zero (InputSeedStrictFace.parameter g) (InputSeedEvalFace.parameter g)
    (InputSeedStrictTargetSeam.face g) s).trans (InputSeedStrictFace.source g s)

/-- The whole right route ends at precisely the same original E word. -/
theorem short_target (s : unitInterval) : shortParameter g (1, s) =
    InputSeedTransitionFace.targetParameter g s :=
  (concatFirst_one (InputSeedStrictFace.parameter g) (InputSeedEvalFace.parameter g)
    (InputSeedStrictTargetSeam.face g) s).trans
      ((InputSeedRawTargetSeam.face g s).symm.trans (InputSeedTransitionFace.target g s))

/-- Every long-route point at seed time zero remains the separately retained ordinary tip. -/
theorem long_zero (r : unitInterval) : longParameter g (r, 0) =
    CutOpenCarrier.tipMinus (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) :=
  concat_fixed (InputSeedInputFace.parameter g) (tailParameter g) (tail_join g) 0 _
    (InputSeedInputFace.zero g)
    (concat_fixed (InputSeedPostFace.parameter g) (InputSeedTransitionFace.parameter g)
      (InputSeedPostTargetSeam.face g) 0 _ (InputSeedPostFace.zero g)
      (InputSeedTransitionFace.zero g)) r

/-- Every long-route point at seed time one remains the separately retained shifted tip. -/
theorem long_one (r : unitInterval) : longParameter g (r, 1) =
    CutOpenCarrier.tipPlus (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) :=
  concat_fixed (InputSeedInputFace.parameter g) (tailParameter g) (tail_join g) 1 _
    (InputSeedInputFace.one g)
    (concat_fixed (InputSeedPostFace.parameter g) (InputSeedTransitionFace.parameter g)
      (InputSeedPostTargetSeam.face g) 1 _ (InputSeedPostFace.one g)
      (InputSeedTransitionFace.one g)) r

/-- The whole short-route source-tip edge agrees with the original ordinary tip. -/
theorem short_zero (r : unitInterval) : shortParameter g (r, 0) =
    CutOpenCarrier.tipMinus (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) :=
  concat_fixed (InputSeedStrictFace.parameter g) (InputSeedEvalFace.parameter g)
    (InputSeedStrictTargetSeam.face g) 0 _
    (InputSeedStrictFace.zero g) (InputSeedEvalFace.zero g) r

/-- The whole short-route terminal-tip edge agrees with the original shifted tip. -/
theorem short_one (r : unitInterval) : shortParameter g (r, 1) =
    CutOpenCarrier.tipPlus (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) :=
  concat_fixed (InputSeedStrictFace.parameter g) (InputSeedEvalFace.parameter g)
    (InputSeedStrictTargetSeam.face g) 1 _
    (InputSeedStrictFace.one g) (InputSeedEvalFace.one g) r

/-- Both full original routes and all their proved whole edges give an actual carrier boundary. -/
def surfaces : CutOpenCarrier.RouteSurfaces (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g) where
  left := longParameter g
  right := shortParameter g
  start := InputSeedStrictFace.sourceParameter g
  finish := InputSeedTransitionFace.targetParameter g
  left_start := long_source g
  left_finish := long_target g
  right_start := short_source g
  right_finish := short_target g
  left_zero := long_zero g
  left_one := long_one g
  right_zero := short_zero g
  right_one := short_one g

/-- Every point of the full long route recovers its original selected native homotopy. -/
theorem long_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
        (ordinary g) (shifted g) n (longParameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.longRoute g).level n (r, x)) s :=
  concat_native (InputSeedInputFace.parameter g) (tailParameter g) (tail_join g)
    (InputSeedWords.inputFirst g)
    ((InputSeedWords.seedSecond g).trans (InputSeedWords.transitionThird g)) n x
    (fun z => (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
        (ordinary g) (shifted g) n z x))
    (fun a b => InputSeedInputFace.native g n a b x)
    (concat_native (InputSeedPostFace.parameter g) (InputSeedTransitionFace.parameter g)
      (InputSeedPostTargetSeam.face g) (InputSeedWords.seedSecond g)
      (InputSeedWords.transitionThird g) n x
      (fun z => (GlobalRawBass.InputIdentityPositive.inclusion X).map n
        (CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
          (ordinary g) (shifted g) n z x))
      (fun a b => InputSeedPostFace.native g n a b x)
      (fun a b => InputSeedTransitionFace.native g n a b x)) r s

/-- Every point of the full short route recovers its original selected native homotopy. -/
theorem short_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
        (ordinary g) (shifted g) n (shortParameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.shortRoute g).level n (r, x)) s :=
  concat_native (InputSeedStrictFace.parameter g) (InputSeedEvalFace.parameter g)
    (InputSeedStrictTargetSeam.face g) (InputSeedWords.seedFirst g)
    (InputSeedWords.evaluationSecond g) n x
    (fun z => (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
        (ordinary g) (shifted g) n z x))
    (fun a b => InputSeedStrictFace.native g n a b x)
    (fun a b => InputSeedEvalFace.native g n a b x) r s

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedRoutes
