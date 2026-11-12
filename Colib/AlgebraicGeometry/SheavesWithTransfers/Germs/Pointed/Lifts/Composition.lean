/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Germs.Pointed.Lifts.Evaluation
public import Colib.AlgebraicGeometry.Correspondences.Support.TargetControl
public import Mathlib.Data.Fintype.EquivFin

/-!
Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Sheaf/Germs/Pointed/Lifts/Composition.lean`, blob
`fc43d3da65e3d22bc9e82c16432ee5035cdd8a52`.
 # Nested actual finite germ witnesses for correspondence composition -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Chow
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  {X Y Z : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)

/-- Choose actual inner witnesses at every intermediate point. The original
geometric generator lift then produces compatible outer and composite witnesses;
their values agree by the original presheaf transfer composition. -/
theorem exists_composed_generator_germ_witnesses
    (A : pullback (C := Scheme) X.hom Y.hom)
    (hA : IsFiniteCorrespondencePoint X.hom Y.hom A) (β : Cor.mk Y ⟶ Cor.mk Z)
    (x : X.left)
    (a : ∀ z : Z.left, (SmoothSite.nisnevichPointFiberCocone Z z F).pt)
    (L : ∀ y : Y.left, PointedGermLiftWitness k P β y a) :
    ∃ (M : PointedGermLiftWitness k P (singleFiniteCorrespondence X.hom Y.hom A hA 1) x
        (fun y => (L y).value k P))
      (N : PointedGermLiftWitness k P
        ((singleFiniteCorrespondence X.hom Y.hom A hA 1) ≫ β) x a),
      N.value k P = M.value k P := by
  classical
  let V := fun y => (SmoothSite.nisnevichNeighborhoodFunctor Y y).obj (L y).source
  let q : ∀ y, V y ⟶ Y := fun y => (L y).source.toBase
  have : ∀ y, Etale (q y).left := by intro y; dsimp only [q]; infer_instance
  obtain ⟨U, n, label, γ, hγ, hc⟩ :=
    Cor.exists_pointed_graph_family_factorization_at_chosen_points k A hA 1 x V q
      (fun y => (L y).source.center) (by
        intro z _
        exact ⟨((integralComponentAt A).subschemeι ≫ pullback.snd X.hom Y.hom) z, (L
(((integralComponentAt A).subschemeι ≫ pullback.snd X.hom Y.hom) z)).source.toBase_center,
          inferInstance⟩)
  let M : PointedGermLiftWitness k P (singleFiniteCorrespondence X.hom Y.hom A hA 1) x
      (fun y => (L y).value k P) :=
    { source := U, size := n, point := label, target := fun i => (L (label i)).source
      branch := γ, graph_eq := hγ, center_control := hc
      representative := fun i => ∑ j,
        P.transfer ((L (label i)).branch j) ((L (label i)).representative j)
      represents := fun _ => rfl }
  let I := Σ i : Fin n, Fin (L (label i)).size
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let branch := fun t : I => γ t.1 ≫ (L (label t.1)).branch t.2
  have hsum : (∑ t : I, branch t ≫
      (Cor.graphFunctor k).map ((L (label t.1)).target t.2).toBase) =
      (Cor.graphFunctor k).map U.toBase ≫
        ((singleFiniteCorrespondence X.hom Y.hom A hA 1) ≫ β) := by
    dsimp only [branch]
    rw [Fintype.sum_sigma]
    simp_rw [Category.assoc, ← Preadditive.comp_sum, (L _).graph_eq,
      ← Category.assoc]
    rw [← Preadditive.sum_comp, hγ, Category.assoc]
  let N : PointedGermLiftWitness k P
      ((singleFiniteCorrespondence X.hom Y.hom A hA 1) ≫ β) x a :=
    { source := U, size := Fintype.card I
      point := fun t => (L (label (e t).1)).point (e t).2
      target := fun t => (L (label (e t).1)).target (e t).2
      branch := fun t => branch (e t)
      graph_eq := (e.sum_comp _).trans hsum
      center_control := by
        intro t
        apply finiteCorrespondences.TargetsIn.comp _ _ _ (hc (e t).1)
        intro y hy
        have hy' : y = (L (label (e t).1)).source.center := hy
        subst y
        exact (L (label (e t).1)).center_control (e t).2
      representative := fun t => (L (label (e t).1)).representative (e t).2
      represents := fun t => (L (label (e t).1)).represents (e t).2 }
  refine ⟨M, N, ?_⟩
  have hv : (∑ t : Fin (Fintype.card I),
      P.transfer (branch (e t)) ((L (label (e t).1)).representative (e t).2)) =
      ∑ i, P.transfer (γ i) (∑ j,
        P.transfer ((L (label i)).branch j) ((L (label i)).representative j)) := by
    refine (e.sum_comp (fun t : I =>
      P.transfer (branch t) ((L (label t.1)).representative t.2))).trans ?_
    rw [Fintype.sum_sigma]
    simp only [branch, transfer_comp, map_sum]
    rfl
  exact congrArg ((SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op U)) hv

end AlgebraicGeometry.PresheafWithTransfers
