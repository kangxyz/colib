/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphRecoveredCycle
import all Colib.AlgebraicGeometry.Correspondences.Graph.FiniteSupportPushforward

/-! # Actual relative graph lift over a source morphism
No source-naturality equation is an input.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow Function.locallyFinsuppWithin
universe u
namespace AlgebraicGeometry.Cor.RelativeGraph
variable (k : Type u) [Field k]
variable {V U Y : SmoothSite (Spec (CommRingCat.of k))} (f : V ⟶ U)

/-- The actual lift followed by the actual target graph. -/
def relativeGraphOverLift : (Cor.mk V ⟶ Cor.mk Y) →+
    (Cor.mk V ⟶ Cor.mk (SmoothSite.product U Y)) :=
  (Preadditive.rightComp (Cor.mk V)
    ((graphFunctor k).map (SmoothSite.productMap f (𝟙 Y)))).comp (relativeGraphLift k V Y)

/-- This actual composite is native pushforward along the closed ambient graph,
even when the target product map itself is not finite. -/
theorem relativeGraphOverLift_val (a : Cor.mk V ⟶ Cor.mk Y) :
    (relativeGraphOverLift k f a).val = finiteCyclePushforward (ambientOver k f) a.val := by
  let L := (finiteCorrespondences V.hom (SmoothSite.product U Y).hom).subtype.comp
    (relativeGraphOverLift k f)
  let R := (finiteCyclePushforward (ambientOver k (Y := Y) f)).comp
    (finiteCorrespondences V.hom Y.hom).subtype
  have he : L = R := by
    apply finiteCorrespondences.addHom_ext_one V.hom Y.hom
    intro z hz
    change (relativeGraphLift k V Y (singleFiniteCorrespondence V.hom Y.hom z hz 1) ≫
      (graphFunctor k).map (SmoothSite.productMap f (𝟙 Y))).val = _
    rw [relativeGraphLift_single, one_smul]
    have h := incidenceTorPairing_finiteImage_single_graph_right_val
      V.hom (SmoothSite.product V Y).hom (SmoothSite.product U Y).hom
      (SmoothSite.productMap f (𝟙 Y)).left
      (MorphismProperty.Over.w (SmoothSite.productMap f (𝟙 Y)))
      (finite_genericPoints k (Cor.mk (SmoothSite.product V Y)))
      (ambientLift k V Y) (ambientOver k (Y := Y) f) rfl z
      (image_admissible k V Y z hz) 1
    simp only [residueDegree_eq_one_of_isPreimmersion, Nat.cast_one, mul_one] at h
    exact h
  exact DFunLike.congr_fun he a

/-- The composite recovers the original correspondence upon target projection. -/
theorem relativeGraphOverLift_comp_snd (a : Cor.mk V ⟶ Cor.mk Y) :
    relativeGraphOverLift k f a ≫ (graphFunctor k).map (SmoothSite.productSnd U Y) = a := by
  change (relativeGraphLift k V Y a ≫
    (graphFunctor k).map (SmoothSite.productMap f (𝟙 Y))) ≫ _ = _
  rw [Category.assoc, ← Functor.map_comp]
  have hp : SmoothSite.productMap f (𝟙 Y) ≫ SmoothSite.productSnd U Y =
      SmoothSite.productSnd V Y := by simp
  rw [hp]
  exact relativeGraphLift_comp_snd k V Y a

end AlgebraicGeometry.Cor.RelativeGraph
