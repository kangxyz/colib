/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityCarrierTop
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityUnitBoundaryNodes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityCarrierSeams

/-!
# Six exact unit and terminal joins in the original global identity carrier

Every equality is proved in the common codiscrete-nerve carrier from the complete actual reference
nodes. The bottom grid columns, contracted top boundary, and both original unit-square clocks
are preserved before evaluation. No native equality is inverted to obtain a carrier equality.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS SmallWaldhausenCategory
open Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open FundamentalGroupoid.OpenCover
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityCarrierUnitSeams
open BoundedFlatPerfectOriginalUnitSquareSimplex

private theorem parameter_nodes {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) {k l : ℕ}
    (N : Fin (k + 1) → CommonReferenceNerve.Node F)
    (M : Fin (l + 1) → CommonReferenceNerve.Node F) (α : ⦋l⦌ ⟶ ⦋k⦌)
    (h : ∀ i, N (α.toOrderHom i) = M i) (z : StdSimplex ℝ (Fin (l + 1))) :
    CommonReferenceNerve.parameter F N (StdSimplex.map α.toOrderHom z) =
      CommonReferenceNerve.parameter F M z := by
  rw [CommonReferenceNerve.parameter_face, funext h]

private theorem binary_parameters {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) {k l : ℕ}
    (N : Fin (k + 1) → CommonReferenceNerve.Node F)
    (M : Fin (l + 1) → CommonReferenceNerve.Node F)
    (α : ⦋2⦌ ⟶ ⦋k⦌) (β : ⦋2⦌ ⟶ ⦋l⦌)
    (h : ∀ i, N (α.toOrderHom i) = M (β.toOrderHom i)) (t : unitInterval) :
    CommonReferenceNerve.parameter F N
        (binaryPath (α.toOrderHom 0) (α.toOrderHom 1) (α.toOrderHom 2) t) =
      CommonReferenceNerve.parameter F M
        (binaryPath (β.toOrderHom 0) (β.toOrderHom 1) (β.toOrderHom 2) t) := by
  let z := binaryPath (k := 2) 0 1 2 t
  have h₁ := CommonReferenceNerve.parameter_face F N α z
  have h₂ := CommonReferenceNerve.parameter_face F M β z
  have e := h₁.trans ((congrArg (fun P ↦ CommonReferenceNerve.parameter F P z)
    (funext h)).trans h₂.symm)
  dsimp only [z] at e
  rw [BoundedFlatCoefficientBassH0Merged.map_any_binary,
    BoundedFlatCoefficientBassH0Merged.map_any_binary] at e
  exact e

private theorem square_left_path (r : unitInterval) :
    squareParameter (r, 0) = rightUnitPath r := by
  rw [square_left]
  have h : ThreeSideSquare.leftTime r = leftHalf (leftHalf r) := by
    apply Subtype.ext
    simp only [coe_leftHalf]
    dsimp [ThreeSideSquare.leftTime]
    ring
  rw [h, trans_leftHalf, trans_leftHalf]

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

private def terminalFace : ⦋4⦌ ⟶ ⦋24⦌ :=
  SimplexCategory.Hom.mk ⟨![20, 21, 22, 23, 24], by decide⟩

private def rightUnitFace : ⦋2⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![2, 3, 7], by decide⟩
private def leftUnitFace : ⦋2⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![5, 6, 7], by decide⟩
private def bottomPlusFace : ⦋2⦌ ⟶ ⦋14⦌ :=
  SimplexCategory.Hom.mk ⟨![6, 7, 8], by decide⟩
private def bottomMinusFace : ⦋2⦌ ⟶ ⦋14⦌ :=
  SimplexCategory.Hom.mk ⟨![12, 13, 14], by decide⟩
private def topPlusFace : ⦋2⦌ ⟶ ⦋24⦌ :=
  SimplexCategory.Hom.mk ⟨![2, 3, 22], by decide⟩
private def topMinusFace : ⦋2⦌ ⟶ ⦋24⦌ :=
  SimplexCategory.Hom.mk ⟨![7, 8, 24], by decide⟩

variable (X : Scheme.{u})

/-- The entire bottom terminal edge is the actual unpaused projection carrier path. -/
theorem bottom_terminal :
    (InputIdentityCarrierBottom.face X).comp
        ⟨fun t : unitInterval ↦ (1, t), by fun_prop⟩ =
      (InputIdentityCarrierProjection.face X).comp
        ⟨fun t : unitInterval ↦ (0, t), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro t
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierBottom.nodes X) (InputIdentityCarrierBottom.parameter.{u} (1, t)) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierProjection.nodes X) (InputIdentityProjection.parameter t)
  rw [InputIdentityCarrierBottom.parameter_one]
  exact parameter_nodes _ _ _ (SimplexGrid.columnFace 4 2 2)
    (InputIdentityUnitBoundaryNodes.bottom_terminal_nodes X) _

/-- All five top terminal nodes are exactly the actual projection nodes, including references. -/
theorem terminal_nodes (i : Fin 5) :
    InputIdentityCarrierTop.nodes X (![20, 21, 22, 23, 24] i) =
      InputIdentityCarrierProjection.nodes X i := by
  fin_cases i
  · exact (InputIdentityCarrierTop.middle_nodes X 10).trans
      (InputIdentityUnitBoundaryNodes.middle_terminal_nodes X 0)
  · exact (InputIdentityCarrierTop.middle_nodes X 11).trans
      (InputIdentityUnitBoundaryNodes.middle_terminal_nodes X 1)
  · exact (InputIdentityCarrierTop.middle_nodes X 12).trans
      (InputIdentityUnitBoundaryNodes.middle_terminal_nodes X 2)
  · exact (InputIdentityCarrierTop.middle_nodes X 13).trans
      (InputIdentityUnitBoundaryNodes.middle_terminal_nodes X 3)
  · exact (InputIdentityCarrierTop.middle_nodes X 14).trans
      (InputIdentityUnitBoundaryNodes.middle_terminal_nodes X 4)

/-- Both contracted top pauses end at the same whole unpaused projection carrier path. -/
theorem top_terminal :
    (InputIdentityCarrierTop.face X).comp
        ⟨fun t : unitInterval ↦ (1, t), by fun_prop⟩ =
      (InputIdentityCarrierProjection.face X).comp
        ⟨fun t : unitInterval ↦ (1, t), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro t
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierTop.nodes X)
      (BoundedFlatCoefficientBassUnitTop.topParameter.{u} (1, t)) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierProjection.nodes X) (InputIdentityProjection.parameter t)
  rw [BoundedFlatCoefficientBassUnitTop.top_one]
  have e := parameter_nodes (InputIdentityNodes.source X) (InputIdentityCarrierTop.nodes X)
    (InputIdentityCarrierProjection.nodes X) terminalFace (terminal_nodes X)
    (InputIdentityProjection.parameter t)
  rw [InputIdentityProjection.parameter, BoundedFlatCoefficientBassH0Merged.map_two_binary] at e
  exact e

/-- The whole plus bottom join retains all actual node references and original unit times. -/
theorem bottom_plus :
    (InputIdentityCarrierBottom.face X).comp
        ⟨fun r : unitInterval ↦ (r, 0), by fun_prop⟩ =
      (InputIdentityCarrierCharts.chartFace X plus plus_projection).comp
        ⟨fun r : unitInterval ↦ (r, 0), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro r
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierBottom.nodes X)
      (InputIdentityCarrierBottom.parameter.{u} (r, 0)) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityNodes.chartSideNodes X plus plus_projection)
      (squareParameter (r, 0))
  rw [InputIdentityCarrierBottom.parameter_left, square_left_path]
  apply binary_parameters _ _ _ bottomPlusFace rightUnitFace ?_ r
  intro i
  fin_cases i
  · exact (InputIdentityUnitBoundaryNodes.plus_bottom_nodes X 0).symm.trans
      (InputIdentityUnitBoundaryNodes.plus_side_actual X 2)
  · exact (InputIdentityUnitBoundaryNodes.plus_bottom_nodes X 1).symm.trans
      (InputIdentityUnitBoundaryNodes.plus_side_actual X 3)
  · exact (InputIdentityUnitBoundaryNodes.plus_bottom_nodes X 2).symm.trans
      (InputIdentityUnitBoundaryNodes.plus_side_actual X 7)

/-- The whole minus bottom join retains all actual node references and original unit times. -/
theorem bottom_minus :
    (InputIdentityCarrierBottom.face X).comp
        ⟨fun r : unitInterval ↦ (r, 1), by fun_prop⟩ =
      (InputIdentityCarrierCharts.chartFace X minus minus_projection).comp
        ⟨fun r : unitInterval ↦ (r, 0), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro r
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierBottom.nodes X)
      (InputIdentityCarrierBottom.parameter.{u} (r, 1)) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityNodes.chartSideNodes X minus minus_projection)
      (squareParameter (r, 0))
  rw [InputIdentityCarrierBottom.parameter_right, square_left_path]
  apply binary_parameters _ _ _ bottomMinusFace rightUnitFace ?_ r
  intro i
  fin_cases i
  · exact (InputIdentityUnitBoundaryNodes.minus_bottom_nodes X 0).symm.trans
      (InputIdentityUnitBoundaryNodes.minus_side_actual X 2)
  · exact (InputIdentityUnitBoundaryNodes.minus_bottom_nodes X 1).symm.trans
      (InputIdentityUnitBoundaryNodes.minus_side_actual X 3)
  · exact (InputIdentityUnitBoundaryNodes.minus_bottom_nodes X 2).symm.trans
      (InputIdentityUnitBoundaryNodes.minus_side_actual X 7)

/-- The whole plus top join retains all actual node references and original unit times. -/
theorem top_plus :
    (InputIdentityCarrierTop.face X).comp
        ⟨fun r : unitInterval ↦ (r, 0), by fun_prop⟩ =
      (InputIdentityCarrierCharts.chartFace X plus plus_projection).comp
        ⟨fun r : unitInterval ↦ (r, 1), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro r
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierTop.nodes X)
      (BoundedFlatCoefficientBassUnitTop.topParameter.{u} (r, 0)) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityNodes.chartSideNodes X plus plus_projection)
      (squareParameter (r, 1))
  rw [BoundedFlatCoefficientBassUnitTop.top_left, square_right_path]
  apply binary_parameters _ _ _ topPlusFace leftUnitFace ?_ r
  intro i
  fin_cases i
  · exact (InputIdentityCarrierTop.plus_nodes X 2).trans
      ((InputIdentityUnitBoundaryNodes.plus_top_nodes X 0).symm.trans
        (InputIdentityUnitBoundaryNodes.plus_side_actual X 5))
  · exact (InputIdentityCarrierTop.plus_nodes X 3).trans
      ((InputIdentityUnitBoundaryNodes.plus_top_nodes X 1).symm.trans
        (InputIdentityUnitBoundaryNodes.plus_side_actual X 6))
  · exact (InputIdentityCarrierTop.plus_nodes X 7).trans
      ((InputIdentityUnitBoundaryNodes.plus_top_nodes X 2).symm.trans
        (InputIdentityUnitBoundaryNodes.plus_side_actual X 7))

/-- The whole minus top join retains all actual node references and original unit times. -/
theorem top_minus :
    (InputIdentityCarrierTop.face X).comp
        ⟨fun r : unitInterval ↦ (r, 1), by fun_prop⟩ =
      (InputIdentityCarrierCharts.chartFace X minus minus_projection).comp
        ⟨fun r : unitInterval ↦ (r, 1), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro r
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierTop.nodes X)
      (BoundedFlatCoefficientBassUnitTop.topParameter.{u} (r, 1)) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityNodes.chartSideNodes X minus minus_projection)
      (squareParameter (r, 1))
  rw [BoundedFlatCoefficientBassUnitTop.top_right, square_right_path]
  apply binary_parameters _ _ _ topMinusFace leftUnitFace ?_ r
  intro i
  fin_cases i
  · exact (InputIdentityCarrierTop.minus_nodes X 2).trans
      ((InputIdentityUnitBoundaryNodes.minus_top_nodes X 0).symm.trans
        (InputIdentityUnitBoundaryNodes.minus_side_actual X 5))
  · exact (InputIdentityCarrierTop.minus_nodes X 3).trans
      ((InputIdentityUnitBoundaryNodes.minus_top_nodes X 1).symm.trans
        (InputIdentityUnitBoundaryNodes.minus_side_actual X 6))
  · exact (InputIdentityCarrierTop.minus_nodes X 7).trans
      ((InputIdentityUnitBoundaryNodes.minus_top_nodes X 2).symm.trans
        (InputIdentityUnitBoundaryNodes.minus_side_actual X 7))

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityCarrierUnitSeams
