/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Points.ChosenGeneratorLift
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.RepresentativeCechGerms
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction

/-!
# Actual finite witnesses for signed germ-tuple evaluation

A witness consists of literal pointed source and target neighborhoods,
actual native signed branch correspondences, their exact graph equation,
all-point center control and sections representing the given tuple. Every
signed prime has such a witness by the genuine chosen-center family lift.
The value uses the original presheaf maps and original point-fiber cocone.
Independence of witnesses and functoriality are separate subsequent proofs.

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Sheaf/Germs/Pointed/Lifts/Evaluation.lean`,
blob `96135b2fd30de953e355aa8c3952cc4934d6d44b`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Chow
open scoped BigOperators

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  {X Y : SmoothSite (Spec (.of k))}

set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)

/-- An actual finite lift diagram and representative sections for an original
all-point germ tuple. No independence or composition law is supplied as a field. -/
structure PointedGermLiftWitness (δ : Cor.mk X ⟶ Cor.mk Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) where
  source : SmoothSite.SmoothPointedEtaleNeighborhood X x
  size : ℕ
  point : Fin size → Y.left
  target : ∀ i, SmoothSite.SmoothPointedEtaleNeighborhood Y (point i)
  branch : ∀ i, Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj source) ⟶
    Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor Y (point i)).obj (target i))
  graph_eq : (∑ i, branch i ≫ (Cor.graphFunctor k).map (target i).toBase) =
    (Cor.graphFunctor k).map source.toBase ≫ δ
  center_control : ∀ i, finiteCorrespondences.TargetsIn (branch i) source.center {(target i).center}
  representative : ∀ i, (F).obj
    (op ((SmoothSite.nisnevichNeighborhoodFunctor Y (point i)).obj (target i)))
  represents : ∀ i, (SmoothSite.nisnevichPointFiberCocone Y (point i) F).ι.app
    (op (target i)) (representative i) = a (point i)

/-- The value uses the actual signed transfers and the original source-point colimit map. -/
def PointedGermLiftWitness.value {δ : Cor.mk X ⟶ Cor.mk Y} {x : X.left}
    {a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt}
    (L : PointedGermLiftWitness k P δ x a) : (SmoothSite.nisnevichPointFiberCocone X x F).pt :=
  (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op L.source)
    (∑ i, P.transfer (L.branch i) (L.representative i))

/-- Every native signed prime has a genuine finite witness at every source point
and for every tuple of original target germs. No sheaf condition is needed here. -/
theorem exists_pointedGermLiftWitness
    (z : pullback (C := Scheme) X.hom Y.hom)
    (hz : IsFiniteCorrespondencePoint X.hom Y.hom z) (c : ℤ) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y F).pt) :
    Nonempty (PointedGermLiftWitness k P
      (singleFiniteCorrespondence X.hom Y.hom z hz c) x a) := by
  classical
  choose R s hs using fun y => SmoothSite.exists_original_germ_representative.{u, 0} F y (a y)
  let V := fun y => (SmoothSite.nisnevichNeighborhoodFunctor Y y).obj (R y)
  let q : ∀ y, V y ⟶ Y := fun y => (R y).toBase
  have : ∀ y, Etale (q y).left := by intro y; dsimp only [q]; infer_instance
  obtain ⟨N, n, label, β, hβ, hcontrol⟩ :=
    Cor.exists_pointed_graph_family_factorization_at_chosen_points k z hz c x V q
      (fun y => (R y).center) (by
        intro w _
        exact ⟨((integralComponentAt z).subschemeι ≫ pullback.snd X.hom Y.hom) w,
          (R _).toBase_center, inferInstance⟩)
  exact ⟨{
    source := N
    size := n
    point := label
    target := fun i => R (label i)
    branch := β
    graph_eq := hβ
    center_control := hcontrol
    representative := fun i => s (label i)
    represents := fun i => hs (label i) }⟩

end AlgebraicGeometry.PresheafWithTransfers
