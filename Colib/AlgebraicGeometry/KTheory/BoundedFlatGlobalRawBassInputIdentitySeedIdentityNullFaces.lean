/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedMovingNull

/-!
# Both prescribed original null faces in the fixed identity seed carrier

The target face pastes the original positive normalization with the corrected positive
moving-null square. The source face pastes the same original normalization after the source
identity with the original polynomial cone cylinder. All initial paths, both moving source
edges, the separate tips, and the common terminal path are equal before native evaluation.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace Topology SSet
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedIdentityNullFaces
open CommonReferenceNerve InputIdentitySeedCarrier InputIdentitySeedLaurentFaces
open InputIdentitySeedLaurentSeams InputIdentitySeedChartSeams

private def sourceUnitFace : ⦋2⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![5, 6, 7], by decide⟩

variable (X : Scheme.{u}) (e : Bool)

/-- The entire source positive edge attaches to the actual source polynomial identity rail. -/
theorem source_polynomial (r : I) :
    sourcePositive X e (r, 1) = InputIdentitySeedCone.cylinder (𝟙 X) e
      (InputIdentitySeedPolynomialFaces.sourceRail X r, 0) := by
  rw [show InputIdentitySeedPolynomialFaces.sourceRail X r =
    parameter (polyRef (𝟙 X)) (InputIdentitySeedPolynomialFaces.K X)
      (binaryPath (k := 7) 5 6 7 r) from rfl,
    InputIdentitySeedPolynomialFaces.cylinder_zero]
  change sheet X e (parameter _ _ (SimplexGrid.parameter.{u + 1} 2 4
    (binaryPath (k := 2) 0 1 2 r, binaryPath (k := 4) 0 1 2 1))) = _
  rw [Path.target, SimplexGrid.parameter_column]
  apply congrArg (sheet X e)
  let z := binaryPath (k := 2) 0 1 2 r
  have hl := parameter_face (InputIdentityNodes.source X)
    (InputIdentityTopNodes.middleNodes X) (SimplexGrid.columnFace 2 4 2) z
  have hr := parameter_face (InputIdentityNodes.source X)
    (InputIdentityTopNodes.plusNodes X) sourceUnitFace z
  have hn (i : Fin 3) :
      InputIdentityTopNodes.middleNodes X ((SimplexGrid.columnFace 2 4 2).toOrderHom i) =
        InputIdentityTopNodes.plusNodes X (sourceUnitFace.toOrderHom i) := by
    fin_cases i
    · exact (InputIdentityTopNodes.plus_five X).symm
    · exact (InputIdentityTopNodes.plus_six X).symm
    · exact (InputIdentityTopNodes.plus_seven X).symm
  have h := hl.trans ((congrArg (fun N ↦ parameter (InputIdentityNodes.source X) N z)
    (funext hn)).trans hr.symm)
  rw [show StdSimplex.map sourceUnitFace.toOrderHom z = binaryPath (k := 7) 5 6 7 r
    from map_binaryPath sourceUnitFace 0 1 2 r] at h
  exact h

/-- The source face retains the whole cylinder at its independent source-identity time. -/
def sourceCone : C(I × I, Carrier (𝟙 X)) :=
  ⟨fun z ↦ InputIdentitySeedCone.cylinder (𝟙 X) e
    (InputIdentitySeedPolynomialFaces.sourceRail X z.1, z.2), by fun_prop⟩

/-- The target moving source edge is the original Laurent identity before normalization. -/
def targetEdge : C(I, Carrier (𝟙 X)) :=
  ⟨fun r ↦ targetPositive X e (r, 0), by fun_prop⟩
/-- The source moving source edge is the original base identity before normalization. -/
def sourceEdge : C(I, Carrier (𝟙 X)) :=
  ⟨fun r ↦ sourcePositive X e (r, 0), by fun_prop⟩
/-- The target normalization ends at the exact left edge of the corrected null square. -/
def targetMiddle : C(I, Carrier (𝟙 X)) :=
  ⟨fun r ↦ targetPositive X e (r, 1), by fun_prop⟩
/-- The source normalization ends at the actual cylinder attachment. -/
def sourceMiddle : C(I, Carrier (𝟙 X)) :=
  ⟨fun r ↦ sourcePositive X e (r, 1), by fun_prop⟩

/-- The whole target positive face, with path time first for literal path pasting. -/
def targetFirst : (targetEdge X e).Homotopy (targetMiddle X e) where
  toFun z := targetPositive X e (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- The whole source positive face retains the original independent source identity time. -/
def sourceFirst : (sourceEdge X e).Homotopy (sourceMiddle X e) where
  toFun z := sourcePositive X e (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- The target face uses precisely the corrected compact-quotient null square. -/
def targetLast : (targetMiddle X e).Homotopy
    (ContinuousMap.const I (InputIdentitySeedCone.tip (𝟙 X) e)) where
  toFun z := (InputIdentitySeedMovingNull.correctedSquare X e).parameter (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := ((InputIdentitySeedMovingNull.correctedSquare X e).left r).trans
    (target_chart X e r).symm
  map_one_left r := (InputIdentitySeedMovingNull.correctedSquare X e).right r

/-- The source cylinder attaches on the full proved source-identity edge. -/
def sourceLast : (sourceMiddle X e).Homotopy
    (ContinuousMap.const I (InputIdentitySeedCone.tip (𝟙 X) e)) where
  toFun z := sourceCone X e (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := (source_polynomial X e r).symm
  map_one_left r := InputIdentitySeedCone.cylinder_one (𝟙 X) e _

/-- The prescribed target null surface retains the original outer half-time subdivision. -/
def target : C(I × I, Carrier (𝟙 X)) :=
  ⟨fun z ↦ ((targetFirst X e).trans (targetLast X e)) (z.2, z.1), by fun_prop⟩

/-- The prescribed source null surface has its exact positive leg and cone-cylinder half. -/
def source : C(I × I, Carrier (𝟙 X)) :=
  ⟨fun z ↦ ((sourceFirst X e).trans (sourceLast X e)) (z.2, z.1), by fun_prop⟩

/-- Every target null starts on the actual moving Laurent identity endpoint. -/
theorem target_left (r : I) : target X e (r, 0) = targetPositive X e (r, 0) :=
  ((targetFirst X e).trans (targetLast X e)).apply_zero r

/-- Every source null starts on the actual moving source identity endpoint. -/
theorem source_left (r : I) : source X e (r, 0) = sourcePositive X e (r, 0) :=
  ((sourceFirst X e).trans (sourceLast X e)).apply_zero r

/-- The target face ends at its own unchanged sheet tip. -/
theorem target_right (r : I) : target X e (r, 1) = InputIdentitySeedCone.tip (𝟙 X) e :=
  ((targetFirst X e).trans (targetLast X e)).apply_one r

/-- The source face has the same tip on this sheet without identifying the two sheets. -/
theorem source_right (r : I) : source X e (r, 1) = InputIdentitySeedCone.tip (𝟙 X) e :=
  ((sourceFirst X e).trans (sourceLast X e)).apply_one r

private theorem corrected_initial (s : I) :
    (InputIdentitySeedMovingNull.correctedSquare X e).parameter (0, s) =
      ((InputIdentitySeedRectangle.positiveMovement (𝟙 X) e).trans
        (InputIdentitySeedRectangle.oldCone (𝟙 X) e)) s := by
  rw [(InputIdentitySeedMovingNull.correctedSquare X e).at_zero]
  change ((InputIdentitySeedMovingNull.firstSwap X e).trans
      (InputIdentitySeedMovingNull.lastSwap X e)) (s, 0) = _
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split
  · exact chart_initial X e _
  · exact InputIdentitySeedPolynomialFaces.targetCone_initial X e _

/-- The complete target initial path is the frozen old null, with both nested subdivisions. -/
theorem target_initial (s : I) :
    target X e (0, s) = InputIdentitySeedNull.oldNull (𝟙 X) e s := by
  change ((targetFirst X e).trans (targetLast X e)) (s, 0) =
    ((InputIdentitySeedRectangle.oldPositive (𝟙 X) e).trans
      ((InputIdentitySeedRectangle.positiveMovement (𝟙 X) e).trans
        (InputIdentitySeedRectangle.oldCone (𝟙 X) e))) s
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split
  · exact InputIdentitySeedLaurentSeams.target_initial X e _
  · exact corrected_initial X e _

/-- The complete source initial path is the frozen new null, with its original cone clock. -/
theorem source_initial (s : I) :
    source X e (0, s) = InputIdentitySeedNull.newNull (𝟙 X) e s := by
  change ((sourceFirst X e).trans (sourceLast X e)) (s, 0) =
    ((InputIdentitySeedRectangle.newPositive (𝟙 X) e).trans
      (InputIdentitySeedRectangle.newCone (𝟙 X) e)) s
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split
  · exact InputIdentitySeedLaurentSeams.source_initial X e _
  · exact InputIdentitySeedPolynomialFaces.sourceCone_initial X e _

/-- Both terminal second halves are the very same unpaused original cone path. -/
theorem terminal_cone (s : I) :
    (InputIdentitySeedMovingNull.correctedSquare X e).parameter (1, s) =
      sourceCone X e (1, s) := by
  rw [(InputIdentitySeedMovingNull.correctedSquare X e).at_one]
  change InputIdentitySeedCone.cylinder (𝟙 X) e
      (InputIdentitySeedPolynomialFaces.targetRail X 1, s) =
    InputIdentitySeedCone.cylinder (𝟙 X) e
      (InputIdentitySeedPolynomialFaces.sourceRail X 1, s)
  exact (InputIdentitySeedPolynomialFaces.targetCone_terminal X e s).trans
    (InputIdentitySeedPolynomialFaces.sourceCone_terminal X e s).symm

/-- The two terminal null paths agree everywhere with their original single outer subdivision. -/
theorem terminal (s : I) : target X e (1, s) = source X e (1, s) := by
  change ((targetFirst X e).trans (targetLast X e)) (s, 1) =
    ((sourceFirst X e).trans (sourceLast X e)) (s, 1)
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split
  · exact InputIdentitySeedLaurentSeams.terminal X e _
  · exact terminal_cone X e _

/-- The whole target null path at each independent identity time. -/
def targetPath (r : I) : Path (targetPositive X e (r, 0))
    (InputIdentitySeedCone.tip (𝟙 X) e) where
  toFun s := target X e (r, s)
  continuous_toFun := by fun_prop
  source' := target_left X e r
  target' := target_right X e r

/-- The whole source null path at each independent identity time. -/
def sourcePath (r : I) : Path (sourcePositive X e (r, 0))
    (InputIdentitySeedCone.tip (𝟙 X) e) where
  toFun s := source X e (r, s)
  continuous_toFun := by fun_prop
  source' := source_left X e r
  target' := source_right X e r

/-- The original old-null endpoint, as its actual complete Laurent carrier point. -/
abbrev oldPoint : Carrier (𝟙 X) :=
  InputIdentitySeedRectangle.sheetMap (𝟙 X) e (StdSimplex.single (2 : Fin 31))

/-- The original new-null endpoint keeps its different original Laurent reference. -/
abbrev newPoint : Carrier (𝟙 X) :=
  InputIdentitySeedRectangle.sheetMap (𝟙 X) e (StdSimplex.single (26 : Fin 31))

/-- The terminal path starts at the common original terminal Laurent reference. -/
def terminalPath : Path (targetPositive X e (1, 0)) (InputIdentitySeedCone.tip (𝟙 X) e) where
  toFun s := target X e (1, s)
  continuous_toFun := by fun_prop
  source' := target_left X e 1
  target' := target_right X e 1

/-- The entire target moving endpoint starts at the original old-null endpoint. -/
def targetBoundary : Path (oldPoint X e)
    (targetPositive X e (1, 0)) where
  toFun r := targetPositive X e (r, 0)
  continuous_toFun := by fun_prop
  source' := (target_left X e 0).symm.trans
    ((target_initial X e 0).trans (InputIdentitySeedNull.oldNull (𝟙 X) e).source)
  target' := rfl

/-- The entire source moving endpoint starts at the original new-null endpoint. -/
def sourceBoundary : Path (newPoint X e)
    (targetPositive X e (1, 0)) where
  toFun r := sourcePositive X e (r, 0)
  continuous_toFun := by fun_prop
  source' := (source_left X e 0).symm.trans
    ((source_initial X e 0).trans (InputIdentitySeedNull.newNull (𝟙 X) e).source)
  target' := (InputIdentitySeedLaurentSeams.terminal X e 0).symm

/-- The prescribed target square has the actual old null and all four exact path boundaries. -/
def targetSquare : CarrierPathSquare.Square (InputIdentitySeedNull.oldNull (𝟙 X) e)
    (terminalPath X e) (targetBoundary X e) (Path.refl (InputIdentitySeedCone.tip (𝟙 X) e)) where
  parameter := target X e
  at_zero := target_initial X e
  at_one _ := rfl
  left := target_left X e
  right := target_right X e

/-- The prescribed source square has the actual new null and the same full terminal path. -/
def sourceSquare : CarrierPathSquare.Square (InputIdentitySeedNull.newNull (𝟙 X) e)
    (terminalPath X e) (sourceBoundary X e) (Path.refl (InputIdentitySeedCone.tip (𝟙 X) e)) where
  parameter := source X e
  at_zero := source_initial X e
  at_one s := (terminal X e s).symm
  left := source_left X e
  right := source_right X e

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedIdentityNullFaces
