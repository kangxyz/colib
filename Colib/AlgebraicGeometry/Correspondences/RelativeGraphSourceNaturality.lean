/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphOverLift
public import Colib.AlgebraicGeometry.Correspondences.Graph.PrecompositionSum

/-!
# Source naturality via actual recovered Tor cycles

The recovered source-component cycles are summed first;
their sum, not each individual component, is identified by projection. The final
additive extension retains every signed coefficient of the original input.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow Function.locallyFinsuppWithin
open scoped BigOperators
universe u
namespace AlgebraicGeometry.Cor.RelativeGraph
variable (k : Type u) [Field k]
variable {V U Y : SmoothSite (Spec (CommRingCat.of k))} (f : V ⟶ U)

private theorem relativeGraphLift_graph_comp_single
    (z : pullback (C := Scheme) U.hom Y.hom)
    (hz : IsFiniteCorrespondencePoint U.hom Y.hom z) :
    (graphFunctor k).map f ≫
        relativeGraphLift k U Y (singleFiniteCorrespondence U.hom Y.hom z hz 1) =
      relativeGraphOverLift k f
        ((graphFunctor k).map f ≫ singleFiniteCorrespondence U.hom Y.hom z hz 1) := by
  classical
  let := (finite_genericPoints k (Cor.mk V)).fintype
  let c : Cor.mk V ⟶ Cor.mk Y :=
    ∑ s : genericPoints V.left, recoveredIncidenceCorrespondence k f s z hz
  have hc : relativeGraphOverLift k f c =
      (graphFunctor k).map f ≫
        relativeGraphLift k U Y (singleFiniteCorrespondence U.hom Y.hom z hz 1) := by
    dsimp only [c]
    rw [map_sum, relativeGraphLift_single, one_smul, graph_comp_single_eq_sum_incidence]
    simp only [one_smul]
    apply Finset.sum_congr rfl
    intro s _
    apply Subtype.ext
    rw [relativeGraphOverLift_val]
    exact recoveredIncidenceCycle_push k f s z hz
  have hp : c = (graphFunctor k).map f ≫
      singleFiniteCorrespondence U.hom Y.hom z hz 1 := by
    calc
      c = relativeGraphOverLift k f c ≫
          (graphFunctor k).map (SmoothSite.productSnd U Y) :=
        (relativeGraphOverLift_comp_snd k f c).symm
      _ = ((graphFunctor k).map f ≫
          relativeGraphLift k U Y (singleFiniteCorrespondence U.hom Y.hom z hz 1)) ≫
          (graphFunctor k).map (SmoothSite.productSnd U Y) :=
        congrArg (fun a => a ≫ (graphFunctor k).map (SmoothSite.productSnd U Y)) hc
      _ = _ := by rw [Category.assoc, relativeGraphLift_comp_snd]
  exact hc.symm.trans (congrArg (relativeGraphOverLift k f) hp)

/-- Every actual signed input correspondence satisfies source naturality.
All original signed coefficients are retained by additive extension. -/
theorem relativeGraphLift_graph_comp (a : Cor.mk U ⟶ Cor.mk Y) :
    (graphFunctor k).map f ≫ relativeGraphLift k U Y a =
      relativeGraphLift k V Y ((graphFunctor k).map f ≫ a) ≫
        (graphFunctor k).map (SmoothSite.productMap f (𝟙 Y)) := by
  let L := (Preadditive.leftComp (Cor.mk (SmoothSite.product U Y))
    ((graphFunctor k).map f)).comp (relativeGraphLift k U Y)
  let R := (relativeGraphOverLift k f).comp
    (Preadditive.leftComp (Cor.mk Y) ((graphFunctor k).map f))
  have h : L = R := by
    apply finiteCorrespondences.addHom_ext_one U.hom Y.hom
    intro z hz
    exact relativeGraphLift_graph_comp_single k f z hz
  exact DFunLike.congr_fun h a

end AlgebraicGeometry.Cor.RelativeGraph
