/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedRawMap
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedConjugation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedWords

/-!
# The entire original raw-transition face in the mixed seed carrier

Actual source evaluation maps the previously proved two-tip original raw conjugation.
Both complete boundary words, both separate tips, and every comparison and output-loop time
survive. This is the third prescribed piece; it supplies no comparison of the two full routes.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen SmallWaldhausenCategory AlgebraicGeometry.RingedSpace SSet
open CategoryTheory.Functor.IdentityAutomorphism
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedTransitionFace
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedCarrier
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original whole raw conjugation keeps both of its scalar coordinates after evaluation. -/
def parameter : C(I × I, Carrier g) :=
  (InputSeedRawMap.map g).hom.comp
    (GlobalRawBass.InputIdentitySeedConjugation.comparison g).toContinuousMap

/-- The complete source seed word is transported by the actual same carrier map. -/
def sourceParameter : C(I, Carrier g) :=
  (InputSeedRawMap.map g).hom.comp
    (GlobalRawBass.InputIdentitySeedConjugation.sourceWord g).toContinuousMap

/-- The complete final seed word retains its original inverse-null/unit/null parentheses. -/
def targetParameter : C(I, Carrier g) :=
  (InputSeedRawMap.map g).hom.comp
    (GlobalRawBass.InputIdentitySeedConjugation.targetWord g).toContinuousMap

/-- The entire first route edge is the prescribed original source word. -/
theorem source (s : I) : parameter g (0, s) = sourceParameter g s :=
  congrArg (InputSeedRawMap.map g)
    (GlobalRawBass.InputIdentitySeedConjugation.comparison_source g s)

/-- The entire final route edge is the prescribed original target word. -/
theorem target (s : I) : parameter g (1, s) = targetParameter g s :=
  congrArg (InputSeedRawMap.map g)
    (GlobalRawBass.InputIdentitySeedConjugation.comparison_target g s)

/-- The whole source-tip edge remains the ordinary tip of the actual mixed carrier. -/
theorem zero (r : I) : parameter g (r, 0) =
    CutOpenCarrier.tipMinus (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) :=
  (congrArg (InputSeedRawMap.map g)
    (GlobalRawBass.InputIdentitySeedConjugation.comparison_zero g r)).trans
      (InputSeedRawMap.map_tipMinus g)

/-- The other whole seed edge retains its distinct shifted tip. -/
theorem one (r : I) : parameter g (r, 1) =
    CutOpenCarrier.tipPlus (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) :=
  (congrArg (InputSeedRawMap.map g)
    (GlobalRawBass.InputIdentitySeedConjugation.comparison_one g r)).trans
      (InputSeedRawMap.map_tipPlus g)

/-- Every original positive-cone value is retained at the actual evaluated source input. -/
theorem positive_native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (parameter g (r, s)) x =
      Path.toContinuousMap ((GlobalRawBass.positiveTransitionHomotopy g).level n
        (r, (evaluation Y).map n x)) s :=
  (InputSeedRawMap.native g n
    (GlobalRawBass.InputIdentitySeedConjugation.comparison g (r, s)) x).trans
      (GlobalRawBass.InputIdentitySeedConjugation.comparison_positiveTransition g n r s
        ((evaluation Y).map n x))

/-- The full original third prescribed homotopy is recovered at all independent times. -/
theorem native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
        (ordinary g) (shifted g) n (parameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.transitionThird g).level n (r, x)) s :=
  (congrArg ((GlobalRawBass.InputIdentityPositive.inclusion X).map n)
    (positive_native g n r s x)).trans
      (GlobalRawBass.positiveTransitionHomotopy_factor g n r s ((evaluation Y).map n x))

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedTransitionFace
