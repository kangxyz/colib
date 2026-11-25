/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvaluationNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvaluationNullUnit
public import Colib.Topology.Path.Homotopy.RetypedUnitComparison
public import Colib.Topology.Prespectrum.RelativeHomotopyTwoSheetConjugationEvaluation

/-!
# The exact original objectwise evaluation seed in its two-tip carrier

The actual four-node unit pasting and both entire original null comparisons supply the
literal two-sheet conjugation. Every original operation and independent clock is retained,
and native evaluation recovers the unchanged positive-cone and whole-cone seed homotopies.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite Topology Convexity
  Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationConjugation
open CommonReferenceNerve InputSeedEvaluationCarrier InputSeedEvaluationNullChart
open InputSeedEvaluationNullRails InputSeedEvaluationNull InputSeedEvaluationNullUnit

private theorem trans_native {Z : Type u} [TopologicalSpace Z] {a b c : Z}
    {E F : LoopPrespectrum.{u}} {f g k : E ⟶ F}
    (n : ℕ) (x : E.space n) (ev : Z → F.space n)
    (p : Path a b) (q : Path b c) (H : Homotopy f g) (K : Homotopy g k)
    (hp : ∀ s, ev (p s) = H.level n (s, x))
    (hq : ∀ s, ev (q s) = K.level n (s, x)) (s : I) :
    ev ((p.trans q) s) = (H.trans K).level n (s, x) := by
  change ev ((p.trans q) s) = (H.trans K).path n x s
  rw [Homotopy.path_trans]
  exact Path.Evaluation.path_trans ev p q (H.path n x) (K.path n x) hp hq s

variable (X : Scheme.{u})

/-- Each original old null retains its nested subdivisions and its own carrier tip. -/
theorem oldNull_native (e : Bool) (n : ℕ) (s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (oldNull X e s) x =
      (InputPositiveNull.originalOldNull X).level n (s, x) := by
  rw [InputPositiveNull.originalOldNull_level]
  let ev := fun z : Carrier X ↦
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n z x
  exact trans_native n x ev _ _ _ _
    (fun t ↦ positiveMovement_native X e n t x)
    (fun t ↦ oldCone_native X e n t x) s

/-- Each original new null keeps the positive leg and its exact cone-cylinder half. -/
theorem newNull_native (e : Bool) (n : ℕ) (s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (newNull X e s) x =
      (InputPositiveNull.originalNewNull X).level n (s, x) := by
  rw [InputPositiveNull.originalNewNull_level]
  let ev := fun z : Carrier X ↦
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n z x
  exact trans_native n x ev _ _ _ _
    (fun t ↦ newPositive_native X e n t x)
    (fun t ↦ newCone_native X e n t x) s

/-- The original source conjugate is a path between the two separately retained tips. -/
abbrev sourceWord := (oldNull X false).symm.trans
  ((InputSeedEvaluationNullUnit.oldUnit X).trans (oldNull X true))

/-- The original target conjugate retains the same separate source and terminal tips. -/
abbrev targetWord := (newNull X false).symm.trans
  ((InputSeedEvaluationNullUnit.newUnit X).trans (newNull X true))

/-- The literal original conjugation uses the complete actual unit and both null surfaces. -/
def comparison : (sourceWord X).Homotopy (targetWord X) :=
  Path.Homotopy.TwoSheetConjugation.comparison
    (InputSeedEvaluationNullUnit.oldUnit X) (InputSeedEvaluationNullUnit.newUnit X)
    (laurentMovement X false) (laurentMovement X true)
    (oldNull X false) (oldNull X true) (newNull X false) (newNull X true)
    (unitComparison X) (pastedNull X false) (pastedNull X true)

/-- The entire source boundary is the unchanged original old conjugate word. -/
theorem comparison_source (s : I) : comparison X (0, s) = sourceWord X s :=
  (comparison X).apply_zero s

/-- The entire target boundary is the unchanged original new conjugate word. -/
theorem comparison_target (s : I) : comparison X (1, s) = targetWord X s :=
  (comparison X).apply_one s

/-- Every comparison-time point on the source tip remains on the ordinary sheet tip. -/
theorem comparison_zero (r : I) : comparison X (r, 0) = InputSeedEvaluationNullCone.tip X false :=
  (comparison X).source r

/-- Every comparison-time point on the terminal tip remains on the shifted sheet tip. -/
theorem comparison_one (r : I) : comparison X (r, 1) = InputSeedEvaluationNullCone.tip X true :=
  (comparison X).target r

/-- All levels and independent times recover the exact chosen positive conjugation. -/
theorem comparison_native (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (comparison X (r, s)) x =
      (InputPositive.conjugation X).level n (r, (s, x)) := by
  let E := prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))
  let F := mappingCone (GlobalRawBass.InputIdentityPositive.chart X)
  let ev : Carrier X → F.space n := fun z ↦
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n z x
  exact NativeTwoSheetConjugation.comparison (E := E) (T := F) n x ev
    (InputSeedEvaluationNullUnit.oldUnit X) (InputSeedEvaluationNullUnit.newUnit X)
    (laurentMovement X false) (laurentMovement X true)
    (oldNull X false) (oldNull X true) (newNull X false) (newNull X true)
    (InputPositiveNull.laurentMovement X)
    (InputPositive.oldUnit X) (InputPositive.newUnit X)
    (InputPositiveNull.originalOldNull X) (InputPositiveNull.originalNewNull X)
    (unitComparison X) (pastedNull X false) (pastedNull X true)
    (InputPositive.unitPasting X) (InputPositiveNull.originalNullComparison X)
    (fun t ↦ oldUnit_native X n t x) (fun t ↦ newUnit_native X n t x)
    (fun t ↦ laurentMovement_native X false n t x)
    (fun t ↦ laurentMovement_native X true n t x)
    (fun t ↦ newNull_native X false n t x) (fun t ↦ newNull_native X true n t x)
    (fun a b ↦ unitComparison_native X n a b x)
    (fun a b ↦ originalNull_native X false n a b x)
    (fun a b ↦ originalNull_native X true n a b x) r s

/-- The original based-loop construction retains every carrier comparison coordinate. -/
theorem comparison_positiveSeed (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
      (ordinary X) (shifted X) n (comparison X (r, s)) x =
      Path.toContinuousMap ((InputPositive.seedHomotopy X).level n (r, x)) s :=
  (comparison_native X n r s x).trans (InputPositive.seedHomotopy_apply X n r s x).symm

/-- Strict positive inclusion recovers the exact original frozen evaluation-seed homotopy. -/
theorem comparison_seed (n : ℕ) (r s : I)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op X))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef X) (chart X) (laurentRef X)
        (ordinary X) (shifted X) n (comparison X (r, s)) x) =
      Path.toContinuousMap ((GlobalBassEvaluation.seedHomotopy X).level n (r, x)) s :=
  (congrArg ((GlobalRawBass.InputIdentityPositive.inclusion X).map n)
    (comparison_positiveSeed X n r s x)).trans
      (InputPositive.seedHomotopy_factor X n r s x)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationConjugation
