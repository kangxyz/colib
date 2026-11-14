/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphLiftCycle

/-!
# Projection recovery for canonical relative graph lifts

This is a native cycle recovery statement, not source
naturality. No flatness or geometric integrality is assumed.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow Function.locallyFinsuppWithin
universe u
namespace AlgebraicGeometry.Cor.RelativeGraph
variable (k : Type u) [Field k]
variable (U Y : SmoothSite (Spec (CommRingCat.of k)))

/-- The ambient target projection retracts the actual closed graph. -/
theorem ambientLift_graphTargetMap_snd :
    ambientLift k U Y ≫ graphTargetMap k U (SmoothSite.productSnd U Y) =
      𝟙 (SmoothSite.product U Y).left := by
  apply pullback.hom_ext
  · simp [graphTargetMap, SmoothSite.product_hom, SmoothSite.productSnd]
  · simp [graphTargetMap, SmoothSite.product_hom, SmoothSite.productSnd]

private theorem relativeGraphLift_comp_snd_single
    (z : pullback (C := Scheme) U.hom Y.hom)
    (hz : IsFiniteCorrespondencePoint U.hom Y.hom z) :
    relativeGraphLift k U Y (singleFiniteCorrespondence U.hom Y.hom z hz 1) ≫
        (graphFunctor k).map (SmoothSite.productSnd U Y) =
      singleFiniteCorrespondence U.hom Y.hom z hz 1 := by
  let B := SmoothSite.product U Y
  have h := incidenceTorPairing_finiteImage_single_graph_right_val
    U.hom B.hom Y.hom (SmoothSite.productSnd U Y).left
    (MorphismProperty.Over.w (SmoothSite.productSnd U Y))
    (finite_genericPoints k (Cor.mk B))
    (ambientLift k U Y) (𝟙 B.left)
    (ambientLift_graphTargetMap_snd k U Y) z (image_admissible k U Y z hz) 1
  apply Subtype.ext
  rw [relativeGraphLift_single, one_smul]
  simp only [residueDegree_eq_one_of_isPreimmersion, Nat.cast_one, mul_one,
    finiteCyclePushforward_single] at h
  exact h

/-- Forgetting the retained source coordinate recovers the original signed cycle. -/
theorem relativeGraphLift_comp_snd (a : Cor.mk U ⟶ Cor.mk Y) :
    relativeGraphLift k U Y a ≫ (graphFunctor k).map (SmoothSite.productSnd U Y) = a := by
  let L := (Preadditive.rightComp (Cor.mk U)
    ((graphFunctor k).map (SmoothSite.productSnd U Y))).comp (relativeGraphLift k U Y)
  have h : L = AddMonoidHom.id _ := by
    apply finiteCorrespondences.addHom_ext_one U.hom Y.hom
    intro z hz
    exact relativeGraphLift_comp_snd_single k U Y z hz
  exact DFunLike.congr_fun h a

end AlgebraicGeometry.Cor.RelativeGraph
