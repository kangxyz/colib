/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Germs.Pointed.Lifts.Independence
public import Colib.AlgebraicGeometry.Sites.Smooth.Germs.Pullback
public import Colib.AlgebraicGeometry.Correspondences.Graph.PointControl

/-!
# Pointed graph lifts for presheaves with transfers
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Chow
universe u v
namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  {X Y : SmoothSite (Spec (.of k))}
set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)
open _root_.AlgebraicGeometry.Scheme.SmoothSite.SmoothPointedEtaleNeighborhood

/-- A representative of just the germ at the image point gives an actual
one-branch graph witness, even on a disconnected source. -/
def PointedGermLiftWitness.graphFromRepresentative (f : X ⟶ Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt)
    (N : SmoothSite.SmoothPointedEtaleNeighborhood Y (f.left x))
    (s : (F).obj (op ((SmoothSite.nisnevichNeighborhoodFunctor Y (f.left x)).obj N)))
    (hs : (SmoothSite.nisnevichPointFiberCocone Y (f.left x) F).ι.app (op N) s = a (f.left x)) :
    PointedGermLiftWitness k P ((Cor.graphFunctor k).map f) x a where
  source := pullbackAlong f x N
  size := 1
  point := fun _ => f.left x
  target := fun _ => N
  branch := fun _ => (Cor.graphFunctor k).map (pullbackAlongToTarget f x N)
  graph_eq := by simp only [Fin.sum_univ_one, ← Functor.map_comp, pullbackAlongToTarget_toBase]
  center_control := by
    intro i A hA z hz
    have h := graphCorrespondenceOfComponents_projection_eq _ _
      (pullbackAlongToTarget f x N).left (MorphismProperty.Over.w _)
      (Cor.finite_genericPoints k (Cor.mk _)) A hA z
    exact h.trans
      ((congrArg (fun t => (pullbackAlongToTarget f x N).left t) hz).trans
        (pullbackAlongToTarget_center f x N))
  representative := fun _ => s
  represents := fun _ => hs

/-- The one-branch actual graph witness evaluates to pullback of the given
original target germ, using the colimit-induced map rather than an assumed law. -/
theorem PointedGermLiftWitness.graphFromRepresentative_value (f : X ⟶ Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt)
    (N : SmoothSite.SmoothPointedEtaleNeighborhood Y (f.left x))
    (s : (F).obj (op ((SmoothSite.nisnevichNeighborhoodFunctor Y (f.left x)).obj N)))
    (hs : (SmoothSite.nisnevichPointFiberCocone Y (f.left x) F).ι.app (op N) s = a (f.left x)) :
    (PointedGermLiftWitness.graphFromRepresentative k P f x a N s hs).value k P =
      SmoothSite.originalGermPullback.{u, 0} F f x (a (f.left x)) := by
  have h := ConcreteCategory.congr_hom (SmoothSite.originalGermPullback_ι.{u, 0} F f x N) s
  rw [ConcreteCategory.comp_apply, hs, ConcreteCategory.comp_apply] at h
  change (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op (pullbackAlong f x N))
      (∑ _ : Fin 1, P.transfer ((Cor.graphFunctor k).map (pullbackAlongToTarget f x N)) s) = _
  rw [Fin.sum_univ_one]
  exact h.symm

/-- Every tuple of original germs admits an actual graph witness. -/
theorem exists_pointedGermLiftWitness_graph (f : X ⟶ Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) :
    Nonempty (PointedGermLiftWitness k P ((Cor.graphFunctor k).map f) x a) := by
  obtain ⟨N, s, hs⟩ := SmoothSite.exists_original_germ_representative.{u, 0} F
    (f.left x) (a (f.left x))
  exact ⟨PointedGermLiftWitness.graphFromRepresentative k P f x a N s hs⟩

/-- For an ordinary Nisnevich sheaf, every actual graph witness has the
canonical pullback value on the original germ at the image point. -/
theorem PointedGermLiftWitness.value_graph
    (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) F)
    (f : X ⟶ Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt)
    (L : PointedGermLiftWitness k P ((Cor.graphFunctor k).map f) x a) :
    L.value k P = SmoothSite.originalGermPullback.{u, 0} F f x (a (f.left x)) := by
  obtain ⟨N, s, hs⟩ := SmoothSite.exists_original_germ_representative.{u, 0} F
    (f.left x) (a (f.left x))
  exact (L.value_eq k P hP
    (PointedGermLiftWitness.graphFromRepresentative k P f x a N s hs)).trans
      (PointedGermLiftWitness.graphFromRepresentative_value k P f x a N s hs)

end AlgebraicGeometry.PresheafWithTransfers
