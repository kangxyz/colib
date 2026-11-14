/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphLiftCycle
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphTargetSquare

/-!
# Target naturality of the canonical relative graph lift

The actual closed support map and the native right-graph residue-degree formula
identify the two composites. No finiteness of the target morphism is required.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow Function.locallyFinsuppWithin
universe u
namespace AlgebraicGeometry.Cor.RelativeGraph
attribute [local instance] isIntegral_integralComponentAt
variable (k : Type u) [Field k]
variable (U : SmoothSite (Spec (CommRingCat.of k)))
variable {Y Z : SmoothSite (Spec (CommRingCat.of k))} (g : Y ⟶ Z)

private theorem relativeGraphLift_comp_graph_single
    (z : pullback (C := Scheme) U.hom Y.hom)
    (hz : IsFiniteCorrespondencePoint U.hom Y.hom z) :
    relativeGraphLift k U Z
        (singleFiniteCorrespondence U.hom Y.hom z hz 1 ≫ (graphFunctor k).map g) =
      relativeGraphLift k U Y (singleFiniteCorrespondence U.hom Y.hom z hz 1) ≫
        (graphFunctor k).map (SmoothSite.productMap (𝟙 U) g) := by
  classical
  let B := SmoothSite.product U Y
  let C := SmoothSite.product U Z
  let A := (integralComponentAt z).subscheme
  let x := genericPoint A
  let i := (integralComponentAt z).subschemeι
  let j := correspondenceGraphPostcompositionMap U.hom Y.hom Z.hom g.left
    (MorphismProperty.Over.w g) z
  let m := i ≫ ambientLift k U Y
  let j' := j ≫ ambientLift k U Z
  have hj : IsFinite j := isFinite_correspondenceGraphPostcompositionMap
    U.hom Y.hom Z.hom g.left (MorphismProperty.Over.w g) z hz
  have hm : IsClosedImmersion m := inferInstance
  have hx : i x = z := genericPointOf_integralComponentAt z
  have hmx : m x = ambientLift k U Y z := congrArg (ambientLift k U Y) hx
  have hmap : m ≫ graphTargetMap k U (SmoothSite.productMap (𝟙 U) g) = j' := by
    change (i ≫ ambientLift k U Y) ≫ _ = j ≫ _
    rw [Category.assoc, ambientLift_graphTargetMap, ← Category.assoc]
    rfl
  have hadm : IsFiniteCorrespondencePoint U.hom B.hom (m x) := by
    rw [hmx]
    exact image_admissible k U Y z hz
  have hr := incidenceTorPairing_finiteImage_single_graph_right_val
    U.hom B.hom C.hom (SmoothSite.productMap (𝟙 U) g).left
    (MorphismProperty.Over.w (SmoothSite.productMap (𝟙 U) g))
    (finite_genericPoints k (Cor.mk B)) m j' hmap x hadm 1
  have hr' :
      (relativeGraphLift k U Y (singleFiniteCorrespondence U.hom Y.hom z hz 1) ≫
        (graphFunctor k).map (SmoothSite.productMap (𝟙 U) g)).val =
        finiteCyclePushforward j' (single x 1) := by
    rw [relativeGraphLift_single, one_smul]
    have he : singleFiniteCorrespondence U.hom B.hom (m x) hadm 1 =
        singleFiniteCorrespondence U.hom B.hom (ambientLift k U Y z)
          (image_admissible k U Y z hz) 1 := by
      apply Subtype.ext
      exact congrArg (fun p => single p (1 : ℤ)) hmx
    simp only [residueDegree_eq_one_of_isPreimmersion, Nat.cast_one, mul_one] at hr
    rw [he] at hr
    exact hr
  apply Subtype.ext
  rw [hr', relativeGraphLift_val]
  have hleft :
      (singleFiniteCorrespondence U.hom Y.hom z hz 1 ≫ (graphFunctor k).map g).val =
        finiteCyclePushforward j (single x 1) :=
    incidenceTorPairing_single_graph_right_val U.hom Y.hom Z.hom g.left
      (MorphismProperty.Over.w g) (finite_genericPoints k (Cor.mk Y)) z hz
  rw [hleft, finiteCyclePushforward_comp_apply]

/-- Retaining the source coordinate commutes with actual graph postcomposition. -/
theorem relativeGraphLift_comp_graph (a : Cor.mk U ⟶ Cor.mk Y) :
    relativeGraphLift k U Z (a ≫ (graphFunctor k).map g) =
      relativeGraphLift k U Y a ≫ (graphFunctor k).map (SmoothSite.productMap (𝟙 U) g) := by
  let L := (relativeGraphLift k U Z).comp
    (Preadditive.rightComp (Cor.mk U) ((graphFunctor k).map g))
  let R := (Preadditive.rightComp (Cor.mk U)
    ((graphFunctor k).map (SmoothSite.productMap (𝟙 U) g))).comp (relativeGraphLift k U Y)
  have h : L = R := by
    apply finiteCorrespondences.addHom_ext_one U.hom Y.hom
    intro z hz
    exact relativeGraphLift_comp_graph_single k U g z hz
  exact DFunLike.congr_fun h a

end AlgebraicGeometry.Cor.RelativeGraph
