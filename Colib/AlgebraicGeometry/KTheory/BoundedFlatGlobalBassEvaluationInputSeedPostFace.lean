/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedPostMap
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvaluationConjugation
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedWords

/-!
# The entire original evaluation seed after raw cone input

The actual raw-post carrier map transports the complete original Y evaluation conjugation.
The original raw-square half precedes each target cylinder, retaining both complete null words
and separate tips. This is the original second piece of the prescribed long route.
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
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedPostFace
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedCarrier
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original whole Y conjugation keeps both coordinates after actual raw cone input. -/
def parameter : C(I × I, Carrier g) :=
  (InputSeedPostMap.map g).hom.comp
    (InputSeedEvaluationConjugation.comparison Y).toContinuousMap

/-- The complete source seed word is transported by the actual same carrier map. -/
def sourceParameter : C(I, Carrier g) :=
  (InputSeedPostMap.map g).hom.comp
    (InputSeedEvaluationConjugation.sourceWord Y).toContinuousMap

/-- The complete final seed word retains its original inverse-null/unit/null parentheses. -/
def targetParameter : C(I, Carrier g) :=
  (InputSeedPostMap.map g).hom.comp
    (InputSeedEvaluationConjugation.targetWord Y).toContinuousMap

/-- The entire source edge is the original Y source word after actual raw cone input. -/
theorem source (s : I) : parameter g (0, s) = sourceParameter g s :=
  congrArg (InputSeedPostMap.map g)
    (InputSeedEvaluationConjugation.comparison_source Y s)

/-- The entire target edge is the original Y target word after actual raw cone input. -/
theorem target (s : I) : parameter g (1, s) = targetParameter g s :=
  congrArg (InputSeedPostMap.map g)
    (InputSeedEvaluationConjugation.comparison_target Y s)

/-- The whole source-tip edge remains the ordinary tip of the actual mixed carrier. -/
theorem zero (r : I) : parameter g (r, 0) =
    CutOpenCarrier.tipMinus (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) :=
  (congrArg (InputSeedPostMap.map g)
    (InputSeedEvaluationConjugation.comparison_zero Y r)).trans
      (InputSeedPostMap.map_tipMinus g)

/-- The other whole seed edge retains its distinct shifted tip. -/
theorem one (r : I) : parameter g (r, 1) =
    CutOpenCarrier.tipPlus (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) :=
  (congrArg (InputSeedPostMap.map g)
    (InputSeedEvaluationConjugation.comparison_one Y r)).trans
      (InputSeedPostMap.map_tipPlus g)

/-- The whole positive seed conjugation follows the independently defined raw positive cone map. -/
theorem positive_native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (parameter g (r, s)) x =
      (GlobalRawBass.InputIdentityPositive.coneMap g).map n
        ((InputPositive.conjugation Y).level n (r, (s, x))) :=
  (InputSeedPostMap.native g n
    (InputSeedEvaluationConjugation.comparison Y (r, s)) x).trans
      (congrArg ((GlobalRawBass.InputIdentityPositive.coneMap g).map n)
        (InputSeedEvaluationConjugation.comparison_native Y n r s x))

private theorem cone_factor (n : ℕ)
    (z : (mappingCone (GlobalRawBass.InputIdentityPositive.chart Y)).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      ((GlobalRawBass.InputIdentityPositive.coneMap g).map n z) =
        (GlobalRawBass.coneMap g).map n
          ((GlobalRawBass.InputIdentityPositive.inclusion Y).map n z) :=
  (congrArg (fun f => f.map n z) (GlobalRawBass.InputIdentityPositive.coneMap_factor g)).symm

/-- The full original second long-route homotopy is recovered at all independent times. -/
theorem native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
        (ordinary g) (shifted g) n (parameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.seedSecond g).level n (r, x)) s :=
  (congrArg ((GlobalRawBass.InputIdentityPositive.inclusion X).map n)
    (positive_native g n r s x)).trans
      ((cone_factor g n _).trans
        ((congrArg ((GlobalRawBass.coneMap g).map n)
          (InputPositive.conjugation_mapped Y n x r s)).trans
            (InputSeedWords.seedSecond_apply g n r s x).symm))

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedPostFace
