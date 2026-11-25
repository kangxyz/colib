/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedMovingNull

/-!
# Native evaluation of the prescribed identity null correction

Both original homotopy clocks survive the initial-pause correction and the compact
quotient descent. The evaluator is used pointwise on the actual two-tip carrier.
-/
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
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedMovingNull
open CommonReferenceNerve InputIdentitySeedCarrier
variable (X : Scheme.{u}) (e : Bool)

/-- The unpaused terminal cone is exactly the original mapping-cone contraction. -/
theorem terminalCone_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n (terminalCone X e s) x =
    (mappingConeHomotopy (InputIdentityPositive.chart X)).level n
      (s, (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)).map n x) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (InputIdentitySeedCone.cylinder (𝟙 X) e
      (InputIdentitySeedPolynomialFaces.targetRail X 1, s)) x = _
  rw [cylinder_native, InputIdentitySeedPolynomialFaces.targetRail_native,
    Homotopy.at_one]; rfl

/-- The actual carrier correction retains the prescribed native reflTrans time. -/
theorem correction_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n (correction X e (r, s)) x =
    (coneSquareIdentityNullComparison (InputIdentityPositive.chart X)).level n
      (r, (s, (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)).map n x)) := by
  change _ = (Homotopy.RelHomotopy.reflTrans
    (mappingConeHomotopy (InputIdentityPositive.chart X))).level n (_, (_, _))
  rw [Homotopy.RelHomotopy.reflTrans_apply_path]
  exact Path.Evaluation.reflTrans
    (fun y : Carrier (𝟙 X) ↦ CutOpenCarrier.nativeEval
      (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n y x)
    (terminalCone X e)
    ((mappingConeHomotopy (InputIdentityPositive.chart X)).path n
      ((boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)).map n x))
    (fun s ↦ terminalCone_native X e n s x) r s

/-- The complete corrected boundary is evaluated before any quotient descent. -/
theorem correctedBoundary_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n (correctedBoundary X e (r, s)) x =
    (CarrierPathSquare.nativeCorrectedBoundary (initialNative X)
      (coneSquareIdentityNullComparison (InputIdentityPositive.chart X))).level n
      (r, (s, (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)).map n x)) :=
  CarrierPathSquare.correctedBoundary_native (initialSquare X e) (correction X e)
    (initialNative X) (coneSquareIdentityNullComparison (InputIdentityPositive.chart X))
    n ((boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)).map n x)
    (fun y ↦ CutOpenCarrier.nativeEval _ _ _ _ _ n y x)
    (fun r s ↦ parameter_native X e n r s x)
    (fun r s ↦ correction_native X e n r s x) r s

/-- The original native identity construction is exactly this corrected boundary descent. -/
private theorem identity_null_eq_boundary {E F : LoopPrespectrum.{u}}
    (f : E ⟶ F) {a : E ⟶ E} {b : F ⟶ F}
    (T : Homotopy (f ≫ b) (a ≫ f)) (A : Homotopy a (𝟙 E)) (B : Homotopy b (𝟙 F))
    (Q : T.Square (coneSquareIdentityTrack f)
      (Homotopy.precomp f B) (A.postcomp f)) :
    (CarrierPathSquare.nativeCorrectedBoundary
      (coneSquareNullMovingSquare f f T (coneSquareIdentityTrack f) A B Q)
      (coneSquareIdentityNullComparison f)).toSquare =
    coneSquareIdentityMovingNullSquare f T A B Q := rfl

/-- The whole corrected carrier surface is the fixed original identity null square. -/
theorem correctedSquare_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n ((correctedSquare X e).parameter (r, s)) x =
    (InputIdentityPositive.nullSquare X).level n
      (r, (s, (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)).map n x)) := by
  have h := CarrierPathSquare.boundarySquare_native (correctedBoundary X e)
    (CarrierPathSquare.nativeCorrectedBoundary (initialNative X)
      (coneSquareIdentityNullComparison (InputIdentityPositive.chart X)))
    n ((boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)).map n x)
    (fun y ↦ CutOpenCarrier.nativeEval _ _ _ _ _ n y x)
    (fun r s ↦ correctedBoundary_native X e n r s x) r s
  rw [identity_null_eq_boundary] at h
  exact h

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedMovingNull
