/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedIdentityNullFaces
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedCorrectedNullNative

/-! Native values of both actual identity-side null surfaces, preserving both original halves. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace Topology SSet
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedIdentityNullFaces
open CommonReferenceNerve InputIdentitySeedCarrier
variable (X : Scheme.{u}) (e : Bool)

/-- The target null surface is the fixed positive cone identity on the unchanged source null. -/
theorem target_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n (target X e (r, s)) x =
    (InputIdentityPositive.coneHomotopy X).level n
      (r, (InputIdentityPositive.sourceNull X).level n (s, x)) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (((targetFirst X e).trans (targetLast X e)) (s, r)) x =
    (InputIdentityPositive.coneHomotopy X).level n (r,
      ((((plusHomotopy X).postcomp (mappingConeInclusion (InputIdentityPositive.chart X))).trans
        (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
          (mappingConeHomotopy (InputIdentityPositive.chart X)))).path n x s))
  rw [ContinuousMap.Homotopy.trans_apply, Homotopy.path_trans, Path.trans_apply]
  split
  · exact InputIdentitySeedLaurentFaces.targetPositive_native X e n r _ x
  · exact InputIdentitySeedMovingNull.correctedSquare_native X e n r _ x

/-- The complete source cylinder is the original contraction after the source identity. -/
theorem sourceCone_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n (sourceCone X e (r, s)) x =
    (mappingConeHomotopy (InputIdentityPositive.chart X)).level n
      (s, (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)).map n
        ((boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X).level n (r, x))) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (InputIdentitySeedCone.cylinder (𝟙 X) e
      (InputIdentitySeedPolynomialFaces.sourceRail X r, s)) x = _
  rw [InputIdentitySeedMovingNull.cylinder_native,
    InputIdentitySeedPolynomialFaces.sourceRail_native]
  rfl

/-- The source null surface is the unchanged complete null after the original source identity. -/
theorem source_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n (source X e (r, s)) x =
    (InputIdentityPositive.sourceNull X).level n
      (s, (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X).level n (r, x)) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (((sourceFirst X e).trans (sourceLast X e)) (s, r)) x =
    ((((plusHomotopy X).postcomp (mappingConeInclusion (InputIdentityPositive.chart X))).trans
      (Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X))
        (mappingConeHomotopy (InputIdentityPositive.chart X)))).path n
          ((boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X).level n (r, x)) s)
  rw [ContinuousMap.Homotopy.trans_apply, Homotopy.path_trans, Path.trans_apply]
  split
  · exact InputIdentitySeedLaurentFaces.sourcePositive_native X e n r _ x
  · exact sourceCone_native X e n r _ x

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedIdentityNullFaces
