/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedCone
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceReanchorAttachment
public import Colib.Topology.Path.RetypedConeNullComparison

/-!
# Both complete original positive rectangles in the global seed carrier

The original 31-node surface and its full-reference unit shift retain every rectangle value.
The actual polynomial column meets its own cone sheet before evaluation. No endpoint-only
identification substitutes for either whole rectangle or either whole polynomial seam.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry.RingedSpace SSet
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedRectangle
open CommonReferenceNerve ModelSimplex InputIdentitySeedCarrier
open BoundedFlatPerfectProjectionRectangleParameters
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The ordinary and unit-shifted original simplex maps, with both actual attachments retained. -/
def sheetMap (e : Bool) : C(StdSimplex ℝ (Fin 31), Carrier g) :=
  (CutOpenCarrier.laurentInclusion (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g)).comp
      (if e then (mapParameter (reanchorNode (commonUnit g))).comp
        (parameter (laurentRef g) (InputDescSimplex.nodes g))
      else parameter (laurentRef g) (InputDescSimplex.nodes g))

/-- Every point of either full simplex has the original native family value. -/
theorem sheetMap_native (e : Bool) (n : ℕ) (z : StdSimplex ℝ (Fin 31))
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (sheetMap g e z) x =
    (mappingConeInclusion (InputIdentityPositive.chart X)).map n
      (prespectrumSimplexFamily (InputDescSimplex.simplex g) n (z, x)) := by
  cases e
  · change CutOpenCarrier.nativeEval _ _ _ _ _ n
      (CutOpenCarrier.laurentInclusion _ _ _ _ _ (parameter _ _ z)) x = _
    rw [CutOpenCarrier.nativeEval_laurentInclusion,
      pointwisePrespectrumFamily_parameter]; rfl
  · change CutOpenCarrier.nativeEval _ _ _ _ _ n
      (CutOpenCarrier.laurentInclusion _ _ _ _ _ (mapParameter (reanchorNode (commonUnit g))
        (parameter _ _ z))) x = _
    rw [CutOpenCarrier.nativeEval_laurentInclusion]
    change (mappingConeInclusion (InputIdentityPositive.chart X)).map n
      (pointwisePrespectrumFamily _ n
        (mapParameter (reanchorNode (commonUnit g)) (parameter _ _ z)) x) = _
    rw [pointwise_reanchor, pointwisePrespectrumFamily_parameter]; rfl

/-- The original old positive binary rail on either sheet. -/
abbrev oldPositive (e : Bool) :=
  (D BoundedFlatCoefficientBassH0Diagram.plusFace).map (sheetMap g e).continuous
/-- The original moving positive square rail on either sheet. -/
abbrev positiveMovement (e : Bool) :=
  (L BoundedFlatCoefficientBassH0Diagram.plusFace).map (sheetMap g e).continuous
/-- The complete nonmonotone polynomial rail on either sheet. -/
abbrev polynomialMovement (e : Bool) :=
  (Ppath BoundedFlatCoefficientBassH0Diagram.plusFace).map (sheetMap g e).continuous
/-- The whole common Laurent square rail, preserving its original reverse/forward cuts. -/
abbrev laurentMovement (e : Bool) :=
  (T BoundedFlatCoefficientBassH0Diagram.plusFace).map (sheetMap g e).continuous
/-- The original new positive binary rail on either sheet. -/
abbrev newPositive (e : Bool) :=
  (K BoundedFlatCoefficientBassH0Diagram.plusFace).map (sheetMap g e).continuous

/-- The entire original geometric rectangle retains its actual source and target words. -/
def rectangle (e : Bool) :
    ((positiveMovement g e).trans (polynomialMovement g e)).Homotopy
      ((oldPositive g e).symm.trans ((laurentMovement g e).trans (newPositive g e))) :=
  ((BoundedFlatPerfectProjectionRectangleParameters.rectangle
    BoundedFlatCoefficientBassH0Diagram.plusFace).map (sheetMap g e)).cast
      (by simp only [Path.map_trans]) (by simp only [Path.map_trans, Path.map_symm])

/-- Every original positive-pasting value is retained on both full-reference sheets. -/
theorem rectangle_native (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (rectangle g e (r, s)) x =
      (InputIdentityPositiveNull.positivePasting g).level n (r, (s, x)) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (sheetMap g e (BoundedFlatPerfectProjectionRectangleParameters.rectangle
      BoundedFlatCoefficientBassH0Diagram.plusFace (r, s))) x = _
  rw [sheetMap_native, InputDescSimplex.plus_rectangle_lift]
  unfold InputIdentityPositiveNull.positivePasting
  symm
  apply Homotopy.RelHomotopy.transport_apply
  all_goals simp only [plusInputLeftTrack, plusInputRightTrack,
    Homotopy.postcomp_trans, Homotopy.postcomp_symm,
    InputIdentityPositiveNull.positiveMovement, InputIdentityPositiveNull.polynomialMovement,
    InputIdentityPositiveNull.oldPositive, InputIdentityPositiveNull.laurentMovement,
    InputIdentityPositiveNull.newPositive]

/-- Each complete polynomial rail meets the actual cone sheet at every movement time. -/
theorem polynomial_seam (e : Bool) (t : I) :
    polynomialMovement g e t = (InputIdentitySeedCone.square g e).parameter (t, 0) := by
  cases e
  · change CutOpenCarrier.laurentInclusion _ _ _ _ _
      (parameter _ _ (Ppath BoundedFlatCoefficientBassH0Diagram.plusFace t)) =
        CutOpenCarrier.cylinderMinus _ _ _ _ _ (movement g t, 0)
    rw [CutOpenCarrier.cylinderMinus_zero, movement_attach]
  · change CutOpenCarrier.laurentInclusion _ _ _ _ _
      (mapParameter (reanchorNode (commonUnit g))
        (parameter _ _ (Ppath BoundedFlatCoefficientBassH0Diagram.plusFace t))) =
        CutOpenCarrier.cylinderPlus _ _ _ _ _ (movement g t, 0)
    rw [CutOpenCarrier.cylinderPlus_zero, shifted_movement_attach]

/-- Original cone paths retyped only along the proved whole polynomial seam. -/
abbrev oldCone (e : Bool) := (InputIdentitySeedCone.square g e).rebaseOld
  (polynomialMovement g e) (polynomial_seam g e)
/-- The new original cone path retains its separately chosen tip. -/
abbrev newCone (e : Bool) := (InputIdentitySeedCone.square g e).rebaseNew
  (polynomialMovement g e) (polynomial_seam g e)

/-- The exact cone comparison retains all collapse and cancellation coordinates after retyping. -/
def coneComparison (e : Bool) : (oldCone g e).Homotopy
    ((polynomialMovement g e).trans (newCone g e)) :=
  ((InputIdentitySeedCone.square g e).rebaseMovement
    (polynomialMovement g e) (polynomial_seam g e)).coneBoundary

/-- Whole endpoint retyping leaves the actual cone-comparison interior unchanged. -/
theorem coneComparison_apply (e : Bool) (r s : I) :
    coneComparison g e (r, s) = InputIdentitySeedCone.boundary g e (r, s) :=
  (InputIdentitySeedCone.square g e).rebaseMovement_coneBoundary_apply
    (polynomialMovement g e) (polynomial_seam g e) r s

/-- The full typed cone comparison is the specified supported conePasting, at every native point. -/
theorem coneComparison_native (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (coneComparison g e (r, s)) x =
        (InputIdentityPositiveNull.conePasting g).level n (r, (s, x)) := by
  rw [coneComparison_apply]
  exact InputIdentitySeedCone.boundary_conePasting g e n r s x

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedRectangle
