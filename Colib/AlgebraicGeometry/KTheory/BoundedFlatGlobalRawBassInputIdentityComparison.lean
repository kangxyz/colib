/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityCarrierCube
public import Colib.Topology.Prespectrum.PushoutSquareFilling

/-!
# The original whole global Bass comparison identity square

The actual six-face carrier cube is evaluated at every native prespectrum level. Its point and
independent structure-time laws give the genuine overlap cylinder, which descends with the two
original whole chart squares. Neither a comparison square nor a cylinder filler is assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentity
local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

variable (X : Scheme.{u})

/-- The genuine overlap retains all six original faces and an independent structure time. -/
def comparisonCylinder : HomotopyPushout.SquareCylinder
    (K (projection.app X))
    (K (projection.app X))
    (inputComparisonHomotopy (𝟙 X)) (coneSquareIdentityTrack (comparison X))
    (Homotopy.precomp (comparison X) (laurentHomotopy X))
    ((spanHomotopy X).postcomp (comparison X))
    (comparisonPlusChart X) (comparisonMinusChart X) where
  level n := (CommonReferenceNerve.compactPrespectrumFamily (InputIdentityNodes.source X)
    (InputIdentityCarrierCube.carrierCube X) n).comp
      ⟨fun z ↦ (![z.1, z.2.1, z.2.2.1], z.2.2.2), by fun_prop⟩
  at_zero n s t x :=
    (CommonReferenceNerve.compactFamily_of_point_eq (InputIdentityNodes.source X)
      (InputIdentityCarrierCube.carrierCube X) (InputIdentityCarrierCharts.inputFace X)
      ![0, s, t] (s, t) (InputIdentityCarrierCube.cube_zero X s t) n x).trans
        (InputIdentityCarrierCharts.inputFace_native X n s t x)
  at_one n s t x :=
    (CommonReferenceNerve.compactFamily_of_point_eq (InputIdentityNodes.source X)
      (InputIdentityCarrierCube.carrierCube X) (InputIdentityCarrierProjection.face X)
      ![1, s, t] (s, t) (InputIdentityCarrierCube.cube_one X s t) n x).trans
        (InputIdentityCarrierProjection.face_native X n s t x)
  bottom n r t x :=
    (CommonReferenceNerve.compactFamily_of_point_eq (InputIdentityNodes.source X)
      (InputIdentityCarrierCube.carrierCube X) (InputIdentityCarrierBottom.face X)
      ![r, 0, t] (r, t) (InputIdentityCarrierCube.cube_bottom X r t) n x).trans
        (InputIdentityCarrierBottom.face_native X n r t x)
  top n r t x :=
    (CommonReferenceNerve.compactFamily_of_point_eq (InputIdentityNodes.source X)
      (InputIdentityCarrierCube.carrierCube X) (InputIdentityCarrierTop.face X)
      ![r, 1, t] (r, t) (InputIdentityCarrierCube.cube_top X r t) n x).trans
        (InputIdentityCarrierTop.face_native X n r t x)
  left n r s x :=
    (CommonReferenceNerve.compactFamily_of_point_eq (InputIdentityNodes.source X)
      (InputIdentityCarrierCube.carrierCube X)
      (InputIdentityCarrierCharts.chartFace X plus plus_projection)
      ![r, s, 0] (r, s) (InputIdentityCarrierCube.cube_left X r s) n x).trans
        (InputIdentityCarrierCharts.plusFace_native X n r s x)
  right n r s x :=
    (CommonReferenceNerve.compactFamily_of_point_eq (InputIdentityNodes.source X)
      (InputIdentityCarrierCube.carrierCube X)
      (InputIdentityCarrierCharts.chartFace X minus minus_projection)
      ![r, s, 1] (r, s) (InputIdentityCarrierCube.cube_right X r s) n x).trans
        (InputIdentityCarrierCharts.minusFace_native X n r s x)
  at_point n r s t :=
    CommonReferenceNerve.compactPrespectrumFamily_point (InputIdentityNodes.source X)
      (InputIdentityCarrierCube.carrierCube X) n ![r, s, t]
  comm n r s t x z :=
    CommonReferenceNerve.compactPrespectrumFamily_structure (InputIdentityNodes.source X)
      (InputIdentityCarrierCube.carrierCube X) n ![r, s, t] x z

/-- The whole square compares the unchanged raw input homotopy with the original identity track. -/
def comparisonSquare :
    (inputComparisonHomotopy (𝟙 X)).Square (coneSquareIdentityTrack (comparison X))
      (Homotopy.precomp (comparison X) (laurentHomotopy X))
      ((spanHomotopy X).postcomp (comparison X)) :=
  HomotopyPushout.squareOfCylinder
    (K (projection.app X))
    (K (projection.app X))
    (inputComparisonHomotopy (𝟙 X)) (coneSquareIdentityTrack (comparison X))
    (Homotopy.precomp (comparison X) (laurentHomotopy X))
    ((spanHomotopy X).postcomp (comparison X))
    (comparisonPlusChart X) (comparisonMinusChart X) (comparisonCylinder X)

/-- Every positive chart value is still the complete original geometric unit square. -/
theorem comparisonSquare_inl (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W (polynomial.obj X))).space n) :
    (comparisonSquare X).level n (r, (s,
      (HomotopyPushout.inl (K (projection.app X))
        (K (projection.app X))).map n x)) =
      (plusSquare X).level n (r, (s, x)) := rfl

/-- The inverse chart retains its separate complete original unit square. -/
theorem comparisonSquare_inr (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W (polynomial.obj X))).space n) :
    (comparisonSquare X).level n (r, (s,
      (HomotopyPushout.inr (K (projection.app X))
        (K (projection.app X))).map n x)) =
      (minusSquare X).level n (r, (s, x)) := rfl

/-- All overlap points descend from the actual carrier cube at the unchanged three coordinates. -/
theorem comparisonSquare_cylinder (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (W X)).space n) :
    (comparisonSquare X).level n (r, (s,
      HomotopyPushout.cylinder (K (projection.app X))
        (K (projection.app X)) n (t, x))) =
      CommonReferenceNerve.compactPrespectrumFamily (InputIdentityNodes.source X)
        (InputIdentityCarrierCube.carrierCube X) n (![r, s, t], x) := rfl

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentity
