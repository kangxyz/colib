/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedUnitSeams
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityPositiveSeed
public import Colib.Topology.Path.Homotopy.RetypedUnitComparison
public import Colib.Topology.Prespectrum.RelativeHomotopyTwoSheetConjugationEvaluation

/-!
# The actual original input-seed conjugation in its two-tip carrier

The whole original unit comparison is retyped along its two proved Laurent rails. The two
original null surfaces then give the literal two-sheet conjugation word. Native evaluation
recovers the chosen positive-cone comparison and its exact frozen full-cone transition image,
with both tips, full references and all independent clocks retained.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedConjugation
open CommonReferenceNerve InputIdentitySeedCarrier InputIdentitySeedRectangle
open InputIdentitySeedRails InputIdentitySeedNull

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

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The complete lower unit word is the actual ordinary rectangle rail. -/
theorem lower_rail (s : I) :
    InputIdentitySeedUnitSeams.lower g s = laurentMovement g false s :=
  InputIdentitySeedUnitSeams.lower_rail g s

/-- The complete upper unit word is the actual shifted rectangle rail. -/
theorem upper_rail (s : I) :
    InputIdentitySeedUnitSeams.upper g s = laurentMovement g true s :=
  InputIdentitySeedUnitSeams.upper_rail g s

/-- The original old unit joins the two exact old-null sources. -/
abbrev oldUnit := Path.RetypedUnitComparison.oldUnit
  (InputIdentitySeedUnitSeams.oldUnit g)
  (InputIdentitySeedUnitSeams.lower g) (InputIdentitySeedUnitSeams.upper g)
  (laurentMovement g false) (laurentMovement g true) (lower_rail g) (upper_rail g)

/-- The original new unit joins the two exact new-null sources. -/
abbrev newUnit := Path.RetypedUnitComparison.newUnit
  (InputIdentitySeedUnitSeams.newUnit g)
  (InputIdentitySeedUnitSeams.lower g) (InputIdentitySeedUnitSeams.upper g)
  (laurentMovement g false) (laurentMovement g true) (lower_rail g) (upper_rail g)

/-- The entire original unit comparison retains precisely the two selected movement rails. -/
def unitComparison : ((oldUnit g).trans (laurentMovement g true)).Homotopy
    ((laurentMovement g false).trans (newUnit g)) :=
  Path.RetypedUnitComparison.comparison
    (InputIdentitySeedUnitSeams.oldUnit g) (InputIdentitySeedUnitSeams.newUnit g)
    (InputIdentitySeedUnitSeams.lower g) (InputIdentitySeedUnitSeams.upper g)
    (laurentMovement g false) (laurentMovement g true) (lower_rail g) (upper_rail g)
    (InputIdentitySeedUnitSeams.unitComparison g)

/-- Endpoint retyping changes neither coordinate of the original unit-pasting parameter. -/
theorem unitComparison_apply (r s : I) : unitComparison g (r, s) =
    InputIdentitySeedUnitSeams.unitMap g (InputIdentitySeedUnitLift.parameter (r, s)) := rfl

/-- Every point of the ten-node family has its original positive-cone value. -/
theorem unitMap_native (n : ℕ) (z : StdSimplex ℝ (Fin 10))
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (InputIdentitySeedUnitSeams.unitMap g z) x =
    (mappingConeInclusion (InputIdentityPositive.chart X)).map n
      (prespectrumSimplexFamily (InputIdentitySeedUnitNodes.simplex g) n (z, x)) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (CutOpenCarrier.laurentInclusion _ _ _ _ _ (parameter _ _ z)) x = _
  rw [CutOpenCarrier.nativeEval_laurentInclusion,
    pointwisePrespectrumFamily_parameter]
  rfl

/-- The full unit surface recovers the original Laurent pasting after cone inclusion. -/
theorem unitComparison_original (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (unitComparison g (r, s)) x =
    (mappingConeInclusion (InputIdentityPositive.chart X)).map n
      ((laurentUnitPasting g).level n (r, (s, x))) :=
  (unitMap_native g n (InputIdentitySeedUnitLift.parameter (r, s)) x).trans
    (congrArg ((mappingConeInclusion (InputIdentityPositive.chart X)).map n)
      (InputIdentitySeedUnitLift.original_lift g n r s x))

/-- The actual positive unit-pasting endpoint transport retains its complete native value. -/
theorem unitPasting_value (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (InputIdentityPositiveSeed.unitPasting g).level n (r, (s, x)) =
    (mappingConeInclusion (InputIdentityPositive.chart X)).map n
      ((laurentUnitPasting g).level n (r, (s, x))) := by
  unfold InputIdentityPositiveSeed.unitPasting
  apply Homotopy.RelHomotopy.transport_apply
  all_goals simp only [Homotopy.postcomp_trans, InputIdentityPositiveSeed.oldUnit,
    InputIdentityPositiveSeed.newUnit, InputIdentityPositiveNull.laurentMovement]

/-- The typed unit comparison is the originally chosen positive unit pasting at all times. -/
theorem unitComparison_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (unitComparison g (r, s)) x =
      (InputIdentityPositiveSeed.unitPasting g).level n (r, (s, x)) :=
  (unitComparison_original g n r s x).trans (unitPasting_value g n r s x).symm

/-- Every original old-unit value survives the whole-rail endpoint replacement. -/
theorem oldUnit_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (oldUnit g s) x =
      (InputIdentityPositiveSeed.oldUnit g).level n (s, x) :=
  (unitMap_native g n (InputIdentitySeedUnitNodes.V s) x).trans
    (congrArg ((mappingConeInclusion (InputIdentityPositive.chart X)).map n)
      (InputIdentitySeedUnitNodes.V_native g n s x))

/-- Every original new-unit value survives the whole-rail endpoint replacement. -/
theorem newUnit_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (newUnit g s) x =
      (InputIdentityPositiveSeed.newUnit g).level n (s, x) :=
  (unitMap_native g n (InputIdentitySeedUnitNodes.W s) x).trans
    (congrArg ((mappingConeInclusion (InputIdentityPositive.chart X)).map n)
      (InputIdentitySeedUnitNodes.W_native g n s x))

/-- Each original old null retains its nested subdivisions and its own carrier tip. -/
theorem oldNull_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (oldNull g e s) x =
      (InputIdentityPositiveNull.originalOldNull g).level n (s, x) := by
  rw [InputIdentityPositiveNull.originalOldNull_level]
  let ev := fun z : Carrier g ↦
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n z x
  exact trans_native n x ev _ _ _ _
    (fun t ↦ oldPositive_native g e n t x)
    (trans_native n x ev _ _ _ _
      (fun t ↦ positiveMovement_native g e n t x)
      (fun t ↦ oldCone_native g e n t x)) s

/-- Each original new null keeps the positive leg and its exact cone-cylinder half. -/
theorem newNull_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (newNull g e s) x =
      (InputIdentityPositiveNull.originalNewNull g).level n (s, x) := by
  rw [InputIdentityPositiveNull.originalNewNull_level]
  let ev := fun z : Carrier g ↦
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n z x
  exact trans_native n x ev _ _ _ _
    (fun t ↦ newPositive_native g e n t x)
    (fun t ↦ newCone_native g e n t x) s

/-- The original source conjugate is a path between the two separately retained tips. -/
abbrev sourceWord := (oldNull g false).symm.trans ((oldUnit g).trans (oldNull g true))

/-- The original target conjugate retains the same separate source and terminal tips. -/
abbrev targetWord := (newNull g false).symm.trans ((newUnit g).trans (newNull g true))

/-- The literal original conjugation uses the complete actual unit and both null surfaces. -/
def comparison : (sourceWord g).Homotopy (targetWord g) :=
  Path.Homotopy.TwoSheetConjugation.comparison (oldUnit g) (newUnit g)
    (laurentMovement g false) (laurentMovement g true)
    (oldNull g false) (oldNull g true) (newNull g false) (newNull g true)
    (unitComparison g) (pastedNull g false) (pastedNull g true)

/-- The entire source boundary is the unchanged original old conjugate word. -/
theorem comparison_source (s : I) : comparison g (0, s) = sourceWord g s :=
  (comparison g).apply_zero s

/-- The entire target boundary is the unchanged original new conjugate word. -/
theorem comparison_target (s : I) : comparison g (1, s) = targetWord g s :=
  (comparison g).apply_one s

/-- Every comparison-time point on the source tip remains on the ordinary sheet tip. -/
theorem comparison_zero (r : I) : comparison g (r, 0) = InputIdentitySeedCone.tip g false :=
  (comparison g).source r

/-- Every comparison-time point on the terminal tip remains on the shifted sheet tip. -/
theorem comparison_one (r : I) : comparison g (r, 1) = InputIdentitySeedCone.tip g true :=
  (comparison g).target r

/-- All levels and independent times recover the exact chosen positive conjugation. -/
theorem comparison_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (comparison g (r, s)) x =
      (InputIdentityPositiveSeed.conjugateComparison g).level n (r, (s, x)) := by
  let E := originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)
  let F := mappingCone (InputIdentityPositive.chart X)
  let ev : Carrier g → F.space n := fun z ↦
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n z x
  exact NativeTwoSheetConjugation.comparison (E := E) (T := F) n x ev
    (oldUnit g) (newUnit g) (laurentMovement g false) (laurentMovement g true)
    (oldNull g false) (oldNull g true) (newNull g false) (newNull g true)
    (InputIdentityPositiveNull.laurentMovement g)
    (InputIdentityPositiveSeed.oldUnit g) (InputIdentityPositiveSeed.newUnit g)
    (InputIdentityPositiveNull.originalOldNull g) (InputIdentityPositiveNull.originalNewNull g)
    (unitComparison g) (pastedNull g false) (pastedNull g true)
    (InputIdentityPositiveSeed.unitPasting g) (InputIdentityPositiveNull.originalNullComparison g)
    (fun t ↦ oldUnit_native g n t x) (fun t ↦ newUnit_native g n t x)
    (fun t ↦ laurentMovement_native g false n t x)
    (fun t ↦ laurentMovement_native g true n t x)
    (fun t ↦ newNull_native g false n t x) (fun t ↦ newNull_native g true n t x)
    (fun a b ↦ unitComparison_native g n a b x)
    (fun a b ↦ originalNull_native g false n a b x)
    (fun a b ↦ originalNull_native g true n a b x) r s

/-- The original based-loop construction retains every carrier comparison coordinate. -/
theorem comparison_positiveTransition (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (comparison g (r, s)) x =
      Path.toContinuousMap ((positiveTransitionHomotopy g).level n (r, x)) s :=
  (comparison_native g n r s x).trans (positiveTransitionHomotopy_apply g n r s x).symm

/-- Strict positive inclusion recovers the exact original frozen transition homotopy. -/
theorem comparison_transition (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
        (ordinary g) (shifted g) n (comparison g (r, s)) x) =
      Path.toContinuousMap ((transitionInputHomotopy g).level n (r, x)) s :=
  (congrArg ((InputIdentityPositive.inclusion X).map n)
    (comparison_positiveTransition g n r s x)).trans
      (positiveTransitionHomotopy_factor g n r s x)

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedConjugation
