/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityCarrierCharts
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityProjection

/-! The original unpaused terminal comparison face in the fixed global reference carrier. -/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen SmallWaldhausenCategory AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityCarrierProjection

open InputIdentityCarrierCharts BoundedFlatCoefficientBassUnitHZeroNodes
open BoundedFlatPerfectOriginalUnitSquareSimplex ModelSimplex
local notation "Wₛ" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

theorem right_route_identity {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (rightFirst f).hom ≫ (rightSecond f).hom = 𝟙 _ := by
  have h : (boundedAboveFlatPerfectNormalizedRightUnitFirst f).hom ≫
      (boundedAboveFlatPerfectNormalizedRightUnitSecond f).hom = 𝟙 _ := by
    simp only [boundedAboveFlatPerfectNormalizedRightUnitFirst,
      boundedAboveFlatPerfectNormalizedRightUnitSecond,
      Iso.trans_hom, eqToIso.hom, isoWhiskerLeft_hom, Category.assoc]
    rw [boundedAboveFlatPerfectNormalizedPullbackCompIso_right_unitality]
    simp
  apply NatTrans.ext
  funext A
  change AsSmall.up.{u, u + 1, 0}.map ((boundedAboveFlatPerfectNormalizedRightUnitFirst f).hom.app
      (AsSmall.down.{u, u + 1, 0}.obj A)) ≫
    AsSmall.up.{u, u + 1, 0}.map ((boundedAboveFlatPerfectNormalizedRightUnitSecond f).hom.app
      (AsSmall.down.{u, u + 1, 0}.obj A)) = 𝟙 _
  exact (AsSmall.up.{u, u + 1, 0}.map_comp _ _).symm.trans
    ((congrArg (fun η ↦ AsSmall.up.{u, u + 1, 0}.map η)
      (NatTrans.congr_app h (AsSmall.down.{u, u + 1, 0}.obj A))).trans
      (AsSmall.up.{u, u + 1, 0}.map_id _))

private theorem rectangle_terminal {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B)
    (F : asSmallCategory (Wₛ A) ⟶
      asSmallCategory (Wₛ C))
    (δ : F.hom.toFunctor ≅ (BoundedFlatPerfectBinarySimplex.sourceMap q p).hom.toFunctor) :
    rectangleSideNodes p q F δ 7 =
      ⟨BoundedFlatPerfectBinarySimplex.targetMap q p,
        δ ≪≫ BoundedFlatPerfectBinarySimplex.total q p⟩ := by
  have h : rightFirst q ≪≫ rightSecond q = Iso.refl _ :=
    Iso.ext (right_route_identity q)
  change preReferenceNode F (sourceMap p) (δ ≪≫ BoundedFlatPerfectBinarySimplex.total q p)
    ⟨sourceMap q, rightFirst q ≪≫ rightSecond q⟩ = _
  rw [h]
  exact pre_reference_source F (sourceMap p) (H := sourceMap q)
    (δ ≪≫ BoundedFlatPerfectBinarySimplex.total q p)

private theorem parameter_single_eq {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) {p q : ℕ}
    (N : Fin (p + 1) → CommonReferenceNerve.Node F)
    (M : Fin (q + 1) → CommonReferenceNerve.Node F)
    (i : Fin (p + 1)) (j : Fin (q + 1)) (h : N i = M j) :
    CommonReferenceNerve.parameter F N (StdSimplex.single i) =
      CommonReferenceNerve.parameter F M (StdSimplex.single j) := by
  let α : ⦋0⦌ ⟶ ⦋p⦌ := SimplexCategory.Hom.mk ⟨fun _ ↦ i, fun _ _ _ ↦ le_rfl⟩
  let β : ⦋0⦌ ⟶ ⦋q⦌ := SimplexCategory.Hom.mk ⟨fun _ ↦ j, fun _ _ _ ↦ le_rfl⟩
  have e : (fun k ↦ N (α.toOrderHom k)) = fun k ↦ M (β.toOrderHom k) :=
    funext fun _ ↦ h
  have en := CommonReferenceNerve.parameter_face F N α (StdSimplex.single 0)
  have em := CommonReferenceNerve.parameter_face F M β (StdSimplex.single 0)
  rw [StdSimplex.map_single, e] at en
  rw [StdSimplex.map_single] at em
  exact en.trans em.symm

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

variable (X : Scheme.{u})

/-- All five actual projection nodes retain the complete base-unit reference. -/
def nodes (i : Fin 5) : InputIdentityNodes.Node X :=
  ModelSimplex.reanchorNode (InputIdentityNodes.sourceToProjection X)
    (InputIdentityProjection.nodes X i)

/-- The entire original projection simplex is preserved by this reference change. -/
theorem projection_family :
    ModelSimplex.ofIsos (InputIdentityNodes.source X) (fun i ↦ (nodes X i).1)
      (fun i ↦ (nodes X i).2) = InputIdentityProjection.simplex X :=
  ModelSimplex.ofIsos_change_reference (InputIdentityNodes.sourceToProjection X) _ _

/-- The terminal face retains the original full cylinder path and ignores only comparison time. -/
def face : C(unitInterval × unitInterval, Carrier X) :=
  ((CommonReferenceNerve.parameter (InputIdentityNodes.source X) (nodes X)).comp
    InputIdentityProjection.parameter.toContinuousMap).comp ContinuousMap.snd

/-- Its whole compact evaluation is the literal unpaused identity track on the original cylinder. -/
theorem face_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (Wₛ X)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputIdentityNodes.source X) (face X)
        n ((s, t), x) =
      (coneSquareIdentityTrack (comparison X)).level n
        (s, HomotopyPushout.cylinder
          (K (projection.app X))
          (K (projection.app X)) n (t, x)) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex (InputIdentityNodes.source X)
    (face X) (nodes X) (s, t) (InputIdentityProjection.parameter t) rfl n x).trans ?_
  rw [projection_family]
  exact InputIdentityProjection.native X n t x

/-- The terminal positive node keeps the full original chart anchor, including unit cancellation. -/
theorem plus_node : nodes X 2 = InputIdentityNodes.chartSideNodes X plus plus_projection 7 := by
  have h : InputIdentityNodes.chartProjectionIso X plus plus_projection =
      InputIdentityNodes.sourceToProjection X := Iso.trans_refl _
  have e := rectangle_terminal (projection.app X) (plus.app X) (InputIdentityNodes.source X)
    (InputIdentityNodes.chartProjectionIso X plus plus_projection)
  rw [h] at e
  exact e.symm

/-- The inverse terminal anchor retains the original projection transport before cancellation. -/
theorem minus_node : nodes X 4 =
    InputIdentityNodes.chartSideNodes X minus minus_projection 7 := by
  have e := rectangle_terminal (projection.app X) (minus.app X) (InputIdentityNodes.source X)
    (InputIdentityNodes.chartProjectionIso X minus minus_projection)
  refine Eq.trans ?_ e.symm
  change (⟨_, InputIdentityNodes.sourceToProjection X ≪≫
    (InputIdentityProjection.sourceIso X ≪≫ BoundedFlatPerfectBinarySimplex.total
      (minus.app X) (projection.app X))⟩ : InputIdentityNodes.Node X) =
    ⟨_, (InputIdentityNodes.sourceToProjection X ≪≫ InputIdentityProjection.sourceIso X) ≪≫
      BoundedFlatPerfectBinarySimplex.total (minus.app X) (projection.app X)⟩
  exact congrArg (fun η ↦ (⟨BoundedFlatPerfectBinarySimplex.targetMap
    (minus.app X) (projection.app X), η⟩ : InputIdentityNodes.Node X))
      (Iso.trans_assoc _ _ _).symm

/-- The entire terminal-positive seam agrees as a continuous path in the actual carrier. -/
theorem plus_seam :
    (face X).comp ⟨fun s : unitInterval ↦ (s, 0), by fun_prop⟩ =
      (chartFace X plus plus_projection).comp
        ⟨fun s : unitInterval ↦ (1, s), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro s
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X) (nodes X)
      (InputIdentityProjection.parameter 0) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityNodes.chartSideNodes X plus plus_projection)
      (squareParameter (1, s))
  rw [Path.source, square_top_path]
  exact parameter_single_eq _ _ _ _ _ (plus_node X)

/-- The inverse terminal seam keeps its distinct original chart and unchanged comparison clock. -/
theorem minus_seam :
    (face X).comp ⟨fun s : unitInterval ↦ (s, 1), by fun_prop⟩ =
      (chartFace X minus minus_projection).comp
        ⟨fun s : unitInterval ↦ (1, s), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro s
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X) (nodes X)
      (InputIdentityProjection.parameter 1) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityNodes.chartSideNodes X minus minus_projection)
      (squareParameter (1, s))
  rw [Path.target, square_top_path]
  exact parameter_single_eq _ _ _ _ _ (minus_node X)

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentityCarrierProjection
