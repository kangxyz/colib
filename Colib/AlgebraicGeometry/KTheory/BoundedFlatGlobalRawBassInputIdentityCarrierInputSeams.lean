/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityCarrierUnitSeams
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1MiddleJoinScalar
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveParameter
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityBoundaryNodes

/-!
# The two original input-surface joins in the global identity carrier

Each original binary support is attached through complete actual dependent nodes. Concatenation,
reversal, and the original three-block association are preserved pointwise in the carrier.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity Topology
open CategoryTheory.Waldhausen SmallWaldhausenCategory
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityCarrierInputSeams

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
  have e := (CommonReferenceNerve.parameter_face F N α z).trans
    ((congrArg (fun ns ↦ CommonReferenceNerve.parameter F ns z) (funext h)).trans
      (CommonReferenceNerve.parameter_face F M β z).symm)
  dsimp only [z] at e
  rw [BoundedFlatCoefficientBassH0Merged.map_any_binary,
    BoundedFlatCoefficientBassH0Merged.map_any_binary] at e
  exact e

private theorem mapped_trans {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a b c : A} {a' b' c' : B} (f : A → C) (g : B → C)
    (p : Path a b) (q : Path b c) (p' : Path a' b') (q' : Path b' c')
    (hp : ∀ t, f (p t) = g (p' t)) (hq : ∀ t, f (q t) = g (q' t))
    (t : unitInterval) : f ((p.trans q) t) = g ((p'.trans q') t) := by
  rw [Path.trans_apply, Path.trans_apply]
  split
  · exact hp _
  · exact hq _

private def sourcePlusInput : ⦋2⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![2, 3, 11], by decide⟩
private def sourceMinusInput : ⦋2⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![2, 14, 22], by decide⟩
private def sourcePlusBottom : ⦋2⦌ ⟶ ⦋14⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 3, 6], by decide⟩
private def sourceMinusBottom : ⦋2⦌ ⟶ ⦋14⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 9, 12], by decide⟩
private def plusRightInput : ⦋2⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![5, 6, 13], by decide⟩
private def plusLeftInput : ⦋2⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![5, 7, 28], by decide⟩
private def minusRightInput : ⦋2⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![16, 17, 24], by decide⟩
private def minusLeftInput : ⦋2⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![16, 18, 30], by decide⟩
private def plusRightTop : ⦋2⦌ ⟶ ⦋24⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 2], by decide⟩
private def plusLeftTop : ⦋2⦌ ⟶ ⦋24⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 4, 12], by decide⟩
private def minusRightTop : ⦋2⦌ ⟶ ⦋24⦌ :=
  SimplexCategory.Hom.mk ⟨![5, 6, 7], by decide⟩
private def minusLeftTop : ⦋2⦌ ⟶ ⦋24⦌ :=
  SimplexCategory.Hom.mk ⟨![5, 9, 14], by decide⟩
private def plusTargetInput : ⦋2⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![26, 27, 28], by decide⟩
private def minusTargetInput : ⦋2⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![26, 29, 30], by decide⟩
private def plusTargetTop : ⦋2⦌ ⟶ ⦋24⦌ :=
  SimplexCategory.Hom.mk ⟨![10, 11, 12], by decide⟩
private def minusTargetTop : ⦋2⦌ ⟶ ⦋24⦌ :=
  SimplexCategory.Hom.mk ⟨![10, 13, 14], by decide⟩

variable (X : Scheme.{u})

private theorem source_plus (t : unitInterval) :
    CommonReferenceNerve.parameter (InputIdentityNodes.source X) (InputIdentityNodes.nodes X)
        (binaryPath (k := 30) 2 3 11 t) =
      CommonReferenceNerve.parameter (InputIdentityNodes.source X)
        (InputIdentityCarrierBottom.nodes X) (binaryPath (k := 14) 0 3 6 t) := by
  apply binary_parameters _ _ _ sourcePlusInput sourcePlusBottom ?_ t
  intro i
  fin_cases i
  · exact InputIdentityBoundaryNodes.h0_plus_source X 0
  · exact InputIdentityBoundaryNodes.h0_plus_source X 1
  · exact InputIdentityBoundaryNodes.h0_plus_source X 2

private theorem source_minus (t : unitInterval) :
    CommonReferenceNerve.parameter (InputIdentityNodes.source X) (InputIdentityNodes.nodes X)
        (binaryPath (k := 30) 2 14 22 t) =
      CommonReferenceNerve.parameter (InputIdentityNodes.source X)
        (InputIdentityCarrierBottom.nodes X) (binaryPath (k := 14) 0 9 12 t) := by
  apply binary_parameters _ _ _ sourceMinusInput sourceMinusBottom ?_ t
  intro i
  fin_cases i
  · exact InputIdentityBoundaryNodes.h0_minus_source X 0
  · exact InputIdentityBoundaryNodes.h0_minus_source X 1
  · exact InputIdentityBoundaryNodes.h0_minus_source X 2

/-- The whole initial bottom join preserves the original two reversed/forward projection clocks. -/
theorem input_bottom :
    (InputIdentityCarrierCharts.inputFace X).comp
        ⟨fun t : unitInterval ↦ (0, t), by fun_prop⟩ =
      (InputIdentityCarrierBottom.face X).comp
        ⟨fun t : unitInterval ↦ (0, t), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro t
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X) (InputIdentityNodes.nodes X)
      (BoundedFlatCoefficientBassH0Diagram.parameter (0, t)) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierBottom.nodes X) (InputIdentityCarrierBottom.parameter.{u} (0, t))
  rw [BoundedFlatCoefficientBassH1Join.h0_parameter_zero,
    InputIdentityCarrierBottom.parameter_zero,
    InputIdentityProjection.parameter, BoundedFlatCoefficientBassH0Merged.map_two_binary]
  exact mapped_trans _ _ _ _ _ _
    (fun s ↦ source_plus X (unitInterval.symm s)) (source_minus X) t

private theorem plus_right (t : unitInterval) :
    CommonReferenceNerve.parameter (InputIdentityNodes.source X) (InputIdentityNodes.nodes X)
        (binaryPath (k := 30) 5 6 13 t) =
      CommonReferenceNerve.parameter (InputIdentityNodes.source X)
        (InputIdentityCarrierTop.nodes X) (binaryPath (k := 24) 0 1 2 t) := by
  apply binary_parameters _ _ _ plusRightInput plusRightTop ?_ t
  intro i
  fin_cases i
  · exact (InputIdentityBoundaryNodes.h0_plus_top X 0).trans
      (InputIdentityCarrierTop.plus_nodes X 0).symm
  · exact (InputIdentityBoundaryNodes.h0_plus_top X 1).trans
      (InputIdentityCarrierTop.plus_nodes X 1).symm
  · exact (InputIdentityBoundaryNodes.h0_plus_top X 2).trans
      (InputIdentityCarrierTop.plus_nodes X 2).symm

private theorem plus_left (t : unitInterval) :
    CommonReferenceNerve.parameter (InputIdentityNodes.source X) (InputIdentityNodes.nodes X)
        (binaryPath (k := 30) 5 7 28 t) =
      CommonReferenceNerve.parameter (InputIdentityNodes.source X)
        (InputIdentityCarrierTop.nodes X) (binaryPath (k := 24) 0 4 12 t) := by
  apply binary_parameters _ _ _ plusLeftInput plusLeftTop ?_ t
  intro i
  fin_cases i
  · exact (InputIdentityBoundaryNodes.h0_plus_top X 0).trans
      (InputIdentityCarrierTop.plus_nodes X 0).symm
  · exact (InputIdentityBoundaryNodes.h0_plus_top X 3).trans
      (InputIdentityCarrierTop.plus_nodes X 4).symm
  · exact (InputIdentityBoundaryNodes.h0_plus_top X 4).trans
      (InputIdentityCarrierTop.plus_nodes X 5).symm

private theorem minus_right (t : unitInterval) :
    CommonReferenceNerve.parameter (InputIdentityNodes.source X) (InputIdentityNodes.nodes X)
        (binaryPath (k := 30) 16 17 24 t) =
      CommonReferenceNerve.parameter (InputIdentityNodes.source X)
        (InputIdentityCarrierTop.nodes X) (binaryPath (k := 24) 5 6 7 t) := by
  apply binary_parameters _ _ _ minusRightInput minusRightTop ?_ t
  intro i
  fin_cases i
  · exact (InputIdentityBoundaryNodes.h0_minus_top X 0).trans
      (InputIdentityCarrierTop.minus_nodes X 0).symm
  · exact (InputIdentityBoundaryNodes.h0_minus_top X 1).trans
      (InputIdentityCarrierTop.minus_nodes X 1).symm
  · exact (InputIdentityBoundaryNodes.h0_minus_top X 2).trans
      (InputIdentityCarrierTop.minus_nodes X 2).symm

private theorem minus_left (t : unitInterval) :
    CommonReferenceNerve.parameter (InputIdentityNodes.source X) (InputIdentityNodes.nodes X)
        (binaryPath (k := 30) 16 18 30 t) =
      CommonReferenceNerve.parameter (InputIdentityNodes.source X)
        (InputIdentityCarrierTop.nodes X) (binaryPath (k := 24) 5 9 14 t) := by
  apply binary_parameters _ _ _ minusLeftInput minusLeftTop ?_ t
  intro i
  fin_cases i
  · exact (InputIdentityBoundaryNodes.h0_minus_top X 0).trans
      (InputIdentityCarrierTop.minus_nodes X 0).symm
  · exact (InputIdentityBoundaryNodes.h0_minus_top X 3).trans
      (InputIdentityCarrierTop.minus_nodes X 4).symm
  · exact (InputIdentityBoundaryNodes.h0_minus_top X 4).trans
      (InputIdentityCarrierTop.minus_nodes X 5).symm

private theorem target_plus (t : unitInterval) :
    CommonReferenceNerve.parameter (InputIdentityNodes.source X) (InputIdentityNodes.nodes X)
        (binaryPath (k := 30) 26 27 28 t) =
      CommonReferenceNerve.parameter (InputIdentityNodes.source X)
        (InputIdentityCarrierTop.nodes X) (binaryPath (k := 24) 10 11 12 t) := by
  apply binary_parameters _ _ _ plusTargetInput plusTargetTop ?_ t
  intro i
  fin_cases i
  · exact (InputIdentityBoundaryNodes.h0_plus_target X 0).trans
      (InputIdentityCarrierTop.middle_nodes X 0).symm
  · exact (InputIdentityBoundaryNodes.h0_plus_target X 1).trans
      (InputIdentityCarrierTop.middle_nodes X 1).symm
  · exact (InputIdentityBoundaryNodes.h0_plus_target X 2).trans
      (InputIdentityCarrierTop.middle_nodes X 2).symm

private theorem target_minus (t : unitInterval) :
    CommonReferenceNerve.parameter (InputIdentityNodes.source X) (InputIdentityNodes.nodes X)
        (binaryPath (k := 30) 26 29 30 t) =
      CommonReferenceNerve.parameter (InputIdentityNodes.source X)
        (InputIdentityCarrierTop.nodes X) (binaryPath (k := 24) 10 13 14 t) := by
  apply binary_parameters _ _ _ minusTargetInput minusTargetTop ?_ t
  intro i
  fin_cases i
  · exact (InputIdentityBoundaryNodes.h0_minus_target X 0).trans
      (InputIdentityCarrierTop.middle_nodes X 0).symm
  · exact (InputIdentityBoundaryNodes.h0_minus_target X 1).trans
      (InputIdentityCarrierTop.middle_nodes X 3).symm
  · exact (InputIdentityBoundaryNodes.h0_minus_target X 2).trans
      (InputIdentityCarrierTop.middle_nodes X 4).symm

/-- The whole original input-top word preserves all three blocks, reversal, and association. -/
theorem input_top :
    (InputIdentityCarrierCharts.inputFace X).comp
        ⟨fun t : unitInterval ↦ (1, t), by fun_prop⟩ =
      (InputIdentityCarrierTop.face X).comp
        ⟨fun t : unitInterval ↦ (0, t), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro t
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X) (InputIdentityNodes.nodes X)
      (BoundedFlatCoefficientBassH0Diagram.parameter (1, t)) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityCarrierTop.nodes X) (BoundedFlatCoefficientBassUnitTop.topParameter.{u} (0, t))
  rw [BoundedFlatCoefficientBassH1Join.h0_parameter_one,
    BoundedFlatCoefficientBassUnitTop.top_zero]
  exact mapped_trans _ _ _ _ _ _
    (mapped_trans _ _ _ _ _ _ (fun s ↦ plus_right X (unitInterval.symm s)) (plus_left X))
    (mapped_trans _ _ _ _ _ _
      (mapped_trans _ _ _ _ _ _ (fun s ↦ target_plus X (unitInterval.symm s)) (target_minus X))
      (fun s ↦ mapped_trans _ _ _ _ _ _
        (fun z ↦ minus_right X (unitInterval.symm z)) (minus_left X) (unitInterval.symm s))) t

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityCarrierInputSeams
