/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedRails
public import Colib.Topology.Prespectrum.RelativeHomotopyNullWordEvaluation

/-!
# Both exact original null-comparison surfaces in the global seed carrier

The original five-stage null comparison is lifted separately on the ordinary and shifted
sheets. Both relative clocks, all path associations, the original rectangle, and the complete
cone-boundary cancellation survive evaluation. The two carrier tips are never identified.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedNull
open CommonReferenceNerve InputIdentitySeedCarrier InputIdentitySeedRectangle InputIdentitySeedRails
variable {X Y : Scheme.{u}} (g : X ⟶ Y) (e : Bool)

/-- The literal original old null has both nested path subdivisions and the chosen sheet tip. -/
abbrev oldNull := (oldPositive g e).trans ((positiveMovement g e).trans (oldCone g e))
/-- The original new null retains its positive leg and actual cone-cylinder half. -/
abbrev newNull := (newPositive g e).trans (newCone g e)

/-- The actual full rectangle gives the unchanged original straight-positive word. -/
def straightPositive :
    (((oldPositive g e).trans (positiveMovement g e)).trans (polynomialMovement g e)).Homotopy
      ((laurentMovement g e).trans (newPositive g e)) :=
  Path.Homotopy.straightPositiveWord (oldPositive g e) (positiveMovement g e)
    (polynomialMovement g e) (laurentMovement g e) (newPositive g e) (rectangle g e)

/-- The complete original five-stage recipe is applied to the actual rectangle and cone square. -/
def pastedNull : (oldNull g e).Homotopy ((laurentMovement g e).trans (newNull g e)) :=
  Path.Homotopy.pastedPositiveNullWord (oldPositive g e) (positiveMovement g e)
    (polynomialMovement g e) (laurentMovement g e) (newPositive g e)
    (oldCone g e) (newCone g e) (rectangle g e) (coneComparison g e)

/-- Every value recovers the exact original pasted-null recipe, including all nested cuts. -/
theorem pastedNull_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (pastedNull g e (r, s)) x =
      (InputIdentityPositiveNull.pastedNullComparison g).level n (r, (s, x)) := by
  let ev : Carrier g → _ := fun z ↦
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n z x
  unfold pastedNull InputIdentityPositiveNull.pastedNullComparison
    InputIdentityPositiveNull.straightPositivePasting
  exact NativeNullWordEvaluation.pastedPositiveNullWord n x ev
    (oldPositive g e) (positiveMovement g e) (polynomialMovement g e)
    (laurentMovement g e) (newPositive g e) (oldCone g e) (newCone g e)
    (InputIdentityPositiveNull.oldPositive g) (InputIdentityPositiveNull.positiveMovement g)
    (InputIdentityPositiveNull.polynomialMovement g) (InputIdentityPositiveNull.laurentMovement g)
    (InputIdentityPositiveNull.newPositive g) (InputIdentityPositiveNull.oldCone g)
    (InputIdentityPositiveNull.newCone g) (rectangle g e)
    (InputIdentityPositiveNull.positivePasting g) (coneComparison g e)
    (InputIdentityPositiveNull.conePasting g)
    (fun t ↦ oldPositive_native g e n t x) (fun t ↦ positiveMovement_native g e n t x)
    (fun t ↦ polynomialMovement_native g e n t x) (fun t ↦ laurentMovement_native g e n t x)
    (fun t ↦ newPositive_native g e n t x) (fun t ↦ oldCone_native g e n t x)
    (fun t ↦ newCone_native g e n t x) (fun a b ↦ rectangle_native g e n a b x)
    (fun a b ↦ coneComparison_native g e n a b x) r s

/-- The actual ofLevels transport retains the whole originally chosen null comparison. -/
theorem originalNull_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (pastedNull g e (r, s)) x =
      (InputIdentityPositiveNull.originalNullComparison g).level n (r, (s, x)) :=
  pastedNull_native g e n r s x

/-- Strict positive inclusion recovers the fixed whole-cone InputNull choice at all coordinates. -/
theorem originalNull_whole (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    (InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
        (ordinary g) (shifted g) n (pastedNull g e (r, s)) x) =
      (InputNull.originalNullComparison g).level n (r, (s, x)) :=
  (congrArg ((InputIdentityPositive.inclusion X).map n)
    (originalNull_native g e n r s x)).trans
      (InputIdentityPositiveNull.originalNullComparison_mapped g n x r s)

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedNull
