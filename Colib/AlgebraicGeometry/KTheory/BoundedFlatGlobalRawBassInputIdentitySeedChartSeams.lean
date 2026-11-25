/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedLaurentSeams
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedPolynomialFaces

/-! Whole actual chart edges, including their full polynomial attachment on each sheet. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedChartSeams
open CommonReferenceNerve InputIdentitySeedCarrier InputIdentitySeedLaurentFaces
open InputIdentitySeedLaurentSeams
open BoundedFlatPerfectOriginalUnitSquareSimplex
  (squareParameter square_top square_right leftUnitPath)

private theorem square_top_path (t : unitInterval) :
    squareParameter (1, t) = (StdSimplex.single 7 : StdSimplex ℝ (Fin 8)) := by
  rw [square_top]
  rw [← Path.extend_apply _ (ThreeSideSquare.topTime t).property]
  rw [Path.extend_trans_of_le_half _ _ (by
    dsimp [ThreeSideSquare.topTime]
    linarith [t.2.2])]
  rw [Path.extend_trans_of_half_le _ _ (by
    dsimp [ThreeSideSquare.topTime]
    linarith [t.2.1])]
  have he : 2 * (2 * (ThreeSideSquare.topTime t : ℝ)) - 1 = (t : ℝ) := by
    dsimp [ThreeSideSquare.topTime]
    ring
  rw [he, Path.extend_apply _ t.property]; rfl

private theorem square_right_path (r : unitInterval) :
    squareParameter (r, 1) = leftUnitPath r := by
  rw [square_right]
  rw [← Path.extend_apply _ (ThreeSideSquare.rightTime r).property]
  rw [Path.extend_trans_of_half_le _ _ (by
    dsimp [ThreeSideSquare.rightTime]
    linarith [r.2.2]), Path.extend_symm_apply]
  have he : 1 - (2 * (ThreeSideSquare.rightTime r : ℝ) - 1) = (r : ℝ) := by
    dsimp [ThreeSideSquare.rightTime]
    ring
  rw [he, Path.extend_apply _ r.property]

variable (X : Scheme.{u})

/-- The whole original plus comparison is the initial chart edge before evaluation. -/
theorem chart_initial (e : Bool) (s : I) :
    chartFace X e (0, s) = InputIdentitySeedRectangle.positiveMovement (𝟙 X) e s := by
  have h := congrArg (sheet X e)
    (DFunLike.congr_fun (InputIdentityCarrierSeams.plus_seam X) s)
  change sheet X e (parameter (InputIdentityNodes.source X) (InputIdentityNodes.nodes X)
    (BoundedFlatCoefficientBassH0Diagram.parameter (s, 0))) = chartFace X e (0, s) at h
  rw [BoundedFlatCoefficientBassH0Merged.h0_parameter_left] at h
  exact h.symm.trans (sheet_raw X e (BoundedFlatPerfectProjectionRectangleParameters.L
    BoundedFlatCoefficientBassH0Diagram.plusFace s))

/-- The entire terminal chart edge is one full reference point, with no added path segment. -/
theorem chart_terminal (e : Bool) (s : I) :
    chartFace X e (1, s) = chartFace X e (1, 0) := by
  change sheet X e (parameter _ _
    (squareParameter (1, s))) =
    sheet X e (parameter _ _ (squareParameter (1, 0)))
  rw [square_top_path s, square_top_path 0]

private def leftUnitFace : ⦋2⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![5, 6, 7], by decide⟩
private def rightUnitFace : ⦋2⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![2, 3, 7], by decide⟩

/-- The full chart edge is attached to the original polynomial identity rail on each sheet. -/
theorem chart_polynomial (e : Bool) (r : I) :
    chartFace X e (r, 1) = InputIdentitySeedCone.cylinder (𝟙 X) e
      (InputIdentitySeedPolynomialFaces.targetRail X r, 0) := by
  rw [show InputIdentitySeedPolynomialFaces.targetRail X r =
    parameter (polyRef (𝟙 X)) (InputIdentitySeedPolynomialFaces.K X)
      (binaryPath (k := 7) 2 3 7 r) from rfl,
    InputIdentitySeedPolynomialFaces.cylinder_zero]
  change sheet X e (parameter _ _
    (squareParameter (r, 1))) = _
  rw [square_right_path]
  apply congrArg (sheet X e)
  let z := binaryPath (k := 2) 0 1 2 r
  have hl := parameter_face (InputIdentityNodes.source X)
    (InputIdentityNodes.chartSideNodes X plus plus_projection) leftUnitFace z
  have hr := parameter_face (InputIdentityNodes.source X)
    (InputIdentityTopNodes.plusNodes X) rightUnitFace z
  have hn (i : Fin 3) :
      InputIdentityNodes.chartSideNodes X plus plus_projection (leftUnitFace.toOrderHom i) =
        InputIdentityTopNodes.plusNodes X (rightUnitFace.toOrderHom i) :=
    (InputIdentityUnitBoundaryNodes.plus_side_actual X (leftUnitFace.toOrderHom i)).symm.trans
      (InputIdentityUnitBoundaryNodes.plus_top_nodes X i)
  have h := hl.trans ((congrArg (fun N ↦ parameter (InputIdentityNodes.source X) N z)
    (funext hn)).trans hr.symm)
  dsimp only [z] at h
  rw [BoundedFlatCoefficientBassH0Merged.map_any_binary,
    BoundedFlatCoefficientBassH0Merged.map_any_binary] at h
  exact h

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedChartSeams
