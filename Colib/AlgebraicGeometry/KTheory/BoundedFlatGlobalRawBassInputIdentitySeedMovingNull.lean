/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedChartSeams
public import Colib.Topology.Prespectrum.ConeSquareMovingNullEvaluation
public import Colib.Topology.Prespectrum.CarrierCorrectedBoundaryEvaluation
public import Colib.Topology.Prespectrum.CarrierSquareDescentEvaluation

/-!
# The complete fixed positive identity null square on both actual seed sheets

The original chart unit square is pasted with the actual polynomial identity cylinder.
The initial constant half is removed by the original reflTrans correction before the
original compact-quotient descent. Every carrier point keeps both independent times.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry.RingedSpace SSet
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedMovingNull
open CommonReferenceNerve InputIdentitySeedCarrier InputIdentitySeedLaurentFaces
open InputIdentitySeedChartSeams
variable (X : Scheme.{u}) (e : Bool)

/-- The actual polynomial identity is crossed with its original selected cone height. -/
def last : C(I × I, Carrier (𝟙 X)) :=
  ⟨fun z ↦ InputIdentitySeedCone.cylinder (𝟙 X) e
    (InputIdentitySeedPolynomialFaces.targetRail X z.1, z.2), by fun_prop⟩

/-- The exact source edge of the original chart family. -/
def leftEdge : C(I, Carrier (𝟙 X)) :=
  ⟨fun r ↦ chartFace X e (r, 0), by fun_prop⟩
/-- The entire chart/polynomial attachment edge. -/
def middleEdge : C(I, Carrier (𝟙 X)) :=
  ⟨fun r ↦ chartFace X e (r, 1), by fun_prop⟩
/-- The original chart with path time first, for its literal half-time pasting. -/
def firstSwap : (leftEdge X e).Homotopy (middleEdge X e) where
  toFun z := chartFace X e (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left _ := rfl
/-- The actual cylinder attaches along the proved entire original chart edge. -/
def lastSwap : (middleEdge X e).Homotopy
    (ContinuousMap.const I (InputIdentitySeedCone.tip (𝟙 X) e)) where
  toFun z := last X e (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := (chart_polynomial X e r).symm
  map_one_left r := InputIdentitySeedCone.cylinder_one (𝟙 X) e _

/-- The full initial moving null keeps the original chart half and cylinder half. -/
def parameter : C(I × I, Carrier (𝟙 X)) :=
  ⟨fun z ↦ ((firstSwap X e).trans (lastSwap X e)) (z.2, z.1), by fun_prop⟩

/-- The Laurent edge is unchanged at every identity time. -/
theorem parameter_left (r : I) : parameter X e (r, 0) = chartFace X e (r, 0) :=
  ((firstSwap X e).trans (lastSwap X e)).apply_zero r
/-- The terminal edge keeps its own original sheet tip. -/
theorem parameter_right (r : I) : parameter X e (r, 1) =
    InputIdentitySeedCone.tip (𝟙 X) e :=
  ((firstSwap X e).trans (lastSwap X e)).apply_one r

/-- The unpaused terminal cone retains the full terminal polynomial reference. -/
def terminalCone : Path (chartFace X e (1, 0)) (InputIdentitySeedCone.tip (𝟙 X) e) where
  toFun s := last X e (1, s)
  continuous_toFun := by fun_prop
  source' := (chart_polynomial X e 1).symm.trans (chart_terminal X e 1)
  target' := InputIdentitySeedCone.cylinder_one (𝟙 X) e _

/-- The initial terminal path has precisely the original constant first half. -/
def upperWord := (Path.refl (chartFace X e (1, 0))).trans (terminalCone X e)

/-- Both terminal path pieces agree in the carrier with their original half-time cuts. -/
theorem parameter_upper (s : I) : parameter X e (1, s) = upperWord X e s := by
  change ((firstSwap X e).trans (lastSwap X e)) (s, 1) =
    ((Path.refl _).trans (terminalCone X e)) s
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split
  · exact chart_terminal X e _
  · rfl

/-- The whole old null path, before correcting the original identity pause. -/
def lowerPath : Path (chartFace X e (0, 0)) (InputIdentitySeedCone.tip (𝟙 X) e) where
  toFun s := parameter X e (0, s)
  continuous_toFun := by fun_prop
  source' := parameter_left X e 0
  target' := parameter_right X e 0
/-- The actual moving Laurent endpoint is kept as its original complete path. -/
def leftPath : Path (chartFace X e (0, 0)) (chartFace X e (1, 0)) where
  toFun r := chartFace X e (r, 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- All four whole original boundary paths are proved before native evaluation. -/
def initialSquare : CarrierPathSquare.Square (lowerPath X e) (upperWord X e)
    (leftPath X e) (Path.refl (InputIdentitySeedCone.tip (𝟙 X) e)) where
  parameter := parameter X e
  at_zero _ := rfl
  at_one := parameter_upper X e
  left := parameter_left X e
  right := parameter_right X e

/-- The literal original initial-pause correction. -/
def correction := Path.Homotopy.reflTrans (terminalCone X e)

/-- The original collapse and horizontally whiskered pause correction retain their clocks. -/
def correctedBoundary : (lowerPath X e).Homotopy
    (((leftPath X e).trans (terminalCone X e)).trans
      (Path.refl (InputIdentitySeedCone.tip (𝟙 X) e)).symm) :=
  (initialSquare X e).toBoundary.trans
    (((Path.Homotopy.refl (leftPath X e)).hcomp (correction X e)).hcomp
      (Path.Homotopy.refl (Path.refl (InputIdentitySeedCone.tip (𝟙 X) e)).symm))

/-- The complete corrected null square is descended through the unchanged compact quotient. -/
def correctedSquare : CarrierPathSquare.Square (lowerPath X e) (terminalCone X e)
    (leftPath X e) (Path.refl (InputIdentitySeedCone.tip (𝟙 X) e)) :=
  CarrierPathSquare.boundarySquare (correctedBoundary X e)

/-- This is the original initial positive moving-null square, before its prescribed correction. -/
abbrev initialNative := coneSquareNullMovingSquare (InputIdentityPositive.chart X)
  (InputIdentityPositive.chart X) (plusSquareHomotopy (𝟙 X))
  (coneSquareIdentityTrack (InputIdentityPositive.chart X))
  (InputIdentity.polynomialHomotopy X) (InputIdentity.laurentHomotopy X)
  (InputIdentity.plusSquare X)

/-- Every carrier cylinder point retains its exact polynomial value and original height. -/
theorem cylinder_native (n : ℕ) (y : |nerve (Codiscrete (Node (polyRef (𝟙 X))))|)
    (s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n
      (InputIdentitySeedCone.cylinder (𝟙 X) e (y, s)) x =
    ReducedMappingCone.cylinder _ _ ((InputIdentityPositive.chart X).map n)
      (s, pointwisePrespectrumFamily (polyRef (𝟙 X)) n y x) := by
  cases e
  · exact CutOpenCarrier.nativeEval_cylinderMinus _ _ _ _ _ n y s x
  · exact CutOpenCarrier.nativeEval_cylinderPlus _ _ _ _ _ n y s x

/-- The whole initial surface recovers the fixed original moving-null square at all coordinates. -/
theorem parameter_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n (parameter X e (r, s)) x =
    (initialNative X).level n
      (r, (s, (boundedAboveFlatPerfectPullbackPrespectrumMap (projection.app X)).map n x)) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (((firstSwap X e).trans (lastSwap X e)) (s, r)) x = _
  rw [ContinuousMap.Homotopy.trans_apply, initialNative, coneSquareNullMovingSquare_apply]
  split
  · exact chartFace_native X e n r _ x
  · exact (cylinder_native X e n _ _ x).trans
      (congrArg (fun y ↦ ReducedMappingCone.cylinder _ _
        ((InputIdentityPositive.chart X).map n) (_, y))
        (InputIdentitySeedPolynomialFaces.targetRail_native X n r x))

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedMovingNull
