/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedStrictMap
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvaluationConjugation
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedWords

/-!
# The entire original strict-input evaluation seed face

The actual strict carrier map transports the complete original X evaluation conjugation.
Both original null words, both distinct tips, and every comparison and output-loop time survive.
This is the first short-route face, with its original strict-seed naturality cast.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite Topology
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedStrictFace
open GlobalSectionChangeIndex CommonReferenceNerve InputSeedCarrier
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original whole X conjugation keeps both coordinates after strict source precomposition. -/
def parameter : C(I × I, Carrier g) :=
  (InputSeedStrictMap.map g).hom.comp
    (InputSeedEvaluationConjugation.comparison X).toContinuousMap

/-- The complete source seed word is transported by the actual same carrier map. -/
def sourceParameter : C(I, Carrier g) :=
  (InputSeedStrictMap.map g).hom.comp
    (InputSeedEvaluationConjugation.sourceWord X).toContinuousMap

/-- The complete final seed word retains its original inverse-null/unit/null parentheses. -/
def targetParameter : C(I, Carrier g) :=
  (InputSeedStrictMap.map g).hom.comp
    (InputSeedEvaluationConjugation.targetWord X).toContinuousMap

/-- The entire first short-route edge is the original X source word after strict input. -/
theorem source (s : I) : parameter g (0, s) = sourceParameter g s :=
  congrArg (InputSeedStrictMap.map g)
    (InputSeedEvaluationConjugation.comparison_source X s)

/-- The entire target edge is the unchanged X target word after strict input. -/
theorem target (s : I) : parameter g (1, s) = targetParameter g s :=
  congrArg (InputSeedStrictMap.map g)
    (InputSeedEvaluationConjugation.comparison_target X s)

/-- The whole source-tip edge remains the ordinary tip of the actual mixed carrier. -/
theorem zero (r : I) : parameter g (r, 0) =
    CutOpenCarrier.tipMinus (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) :=
  (congrArg (InputSeedStrictMap.map g)
    (InputSeedEvaluationConjugation.comparison_zero X r)).trans
      (InputSeedStrictMap.map_tipMinus g)

/-- The other whole seed edge retains its distinct shifted tip. -/
theorem one (r : I) : parameter g (r, 1) =
    CutOpenCarrier.tipPlus (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) :=
  (congrArg (InputSeedStrictMap.map g)
    (InputSeedEvaluationConjugation.comparison_one X r)).trans
      (InputSeedStrictMap.map_tipPlus g)

/-- Every original positive value is retained at the actual strict source input. -/
theorem positive_native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (parameter g (r, s)) x =
      Path.toContinuousMap ((InputPositive.seedHomotopy X).level n
        (r, (sectionMap g).map n x)) s :=
  (InputSeedStrictMap.native g n
    (InputSeedEvaluationConjugation.comparison X (r, s)) x).trans
      (InputSeedEvaluationConjugation.comparison_positiveSeed X n r s
        ((sectionMap g).map n x))

/-- The full original first short-route homotopy retains all independent times. -/
theorem native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
        (ordinary g) (shifted g) n (parameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.seedFirst g).level n (r, x)) s :=
  (congrArg ((GlobalRawBass.InputIdentityPositive.inclusion X).map n)
    (positive_native g n r s x)).trans
      ((InputPositive.seedHomotopy_factor X n r s ((sectionMap g).map n x)).trans
        ((GlobalBassEvaluation.seedHomotopy_apply X n r s ((sectionMap g).map n x)).trans
          (InputSeedWords.seedFirst_apply g n r s x).symm))

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedStrictFace
