/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Germs.FiniteRepresentatives.LiftIndependence
public import Colib.AlgebraicGeometry.Correspondences.Graph.TargetControl
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.CommonRefinement
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Refinement

/-!
Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Sheaf/Germs/FiniteRepresentatives/SourceIndependence.lean`, blob
`bdf18ee5fb7a759876f106f6effb9440755b24ec`.

# Independence of the actual source neighborhood for fixed representatives

Two controlled lifts on different pointed source neighborhoods are compared on
their actual common pullback. Flat graph precomposition preserves their target
center controls, and the original point-fiber cocone transports the resulting
center-germ equality back to the two original representatives.

The target representative family is fixed. Neither common finite support nor a
new point-fiber or transfer-envelope structure is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Chow

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] (P : PresheafWithTransfers.{max (u + 1) v} k)
  {X Y : SmoothSite (Spec (.of k))} {n : ℕ} (y : Fin n → Y.left)
  (R : ∀ i, SmoothSite.SmoothPointedEtaleNeighborhood Y (y i))

set_option quotPrecheck false in
local notation "F" => ((toPresheaf k).obj P)
set_option quotPrecheck false in
local notation "V" => (fun i => (SmoothSite.nisnevichNeighborhoodFunctor Y (y i)).obj (R i))
set_option quotPrecheck false in
local notation "W" => (SmoothSite.finiteCoproduct V)
set_option quotPrecheck false in
local notation "q" => (SmoothSite.finiteCoproductDesc (fun i => (R i).toBase))
set_option quotPrecheck false in
local notation "T" => (Set.range (fun i => (SmoothSite.finiteCoproductι V i).left (R i).center))

/-- Lifts of one correspondence on different actual source neighborhoods give
the same original source-point class for a fixed finite target representative
family. The common source, support and matching Čech germs are all constructed. -/
theorem transfer_cocone_eq_of_finite_representatives_common_source
    (x : X.left) (N M : SmoothSite.SmoothPointedEtaleNeighborhood X x)
    (δ : Cor.mk X ⟶ Cor.mk Y)
    (α : Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj N) ⟶ Cor.mk W)
    (α' : Cor.mk ((SmoothSite.nisnevichNeighborhoodFunctor X x).obj M) ⟶ Cor.mk W)
    (hα : α ≫ (Cor.graphFunctor k).map q = (Cor.graphFunctor k).map N.toBase ≫ δ)
    (hα' : α' ≫ (Cor.graphFunctor k).map q = (Cor.graphFunctor k).map M.toBase ≫ δ)
    (hfirst : finiteCorrespondences.TargetsIn α N.center T)
    (hfirst' : finiteCorrespondences.TargetsIn α' M.center T)
    (a : ∀ z : Y.left, (SmoothSite.nisnevichPointFiberCocone Y z F).pt)
    (s : P.sections (Cor.mk W))
    (hs : ∀ i, (SmoothSite.nisnevichPointFiberCocone Y (y i) F).ι.app (op (R i))
      ((F).map (SmoothSite.finiteCoproductι V i).op s) = a (y i)) :
    (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op N) (P.transfer α s) =
      (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op M) (P.transfer α' s) := by
  let C := SmoothSite.SmoothPointedEtaleNeighborhood.common N M
  let f := (SmoothSite.nisnevichNeighborhoodFunctor X x).map
    (SmoothSite.SmoothPointedEtaleNeighborhood.commonFst N M)
  let g := (SmoothSite.nisnevichNeighborhoodFunctor X x).map
    (SmoothSite.SmoothPointedEtaleNeighborhood.commonSnd N M)
  let β := (Cor.graphFunctor k).map f ≫ α
  let β' := (Cor.graphFunctor k).map g ≫ α'
  have hfbase : f ≫ N.toBase = C.toBase :=
    SmoothSite.SmoothPointedEtaleNeighborhood.map_toBase
      (SmoothSite.SmoothPointedEtaleNeighborhood.commonFst N M)
  have hgbase : g ≫ M.toBase = C.toBase :=
    SmoothSite.SmoothPointedEtaleNeighborhood.map_toBase
      (SmoothSite.SmoothPointedEtaleNeighborhood.commonSnd N M)
  have heq : β ≫ (Cor.graphFunctor k).map q = β' ≫ (Cor.graphFunctor k).map q := by
    dsimp only [β, β']
    rw [Category.assoc, hα, ← Category.assoc, ← Functor.map_comp, hfbase,
      Category.assoc, hα', ← Category.assoc, ← Functor.map_comp, hgbase]
  have hβ : finiteCorrespondences.TargetsIn β C.center T :=
    Cor.targetsIn_graph_comp k α f N.center C.center
      (SmoothSite.SmoothPointedEtaleNeighborhood.map_center
        (SmoothSite.SmoothPointedEtaleNeighborhood.commonFst N M)) T hfirst
  have hβ' : finiteCorrespondences.TargetsIn β' C.center T :=
    Cor.targetsIn_graph_comp k α' g M.center C.center
      (SmoothSite.SmoothPointedEtaleNeighborhood.map_center
        (SmoothSite.SmoothPointedEtaleNeighborhood.commonSnd N M)) T hfirst'
  have hcenter := transfer_germ_eq_of_finite_representatives_auto_support
    k P y R β β' heq C.center hβ hβ' a s hs
  have hC := SmoothSite.nisnevichPointFiberCocone_eq_of_center_germ_eq F C
    (P.transfer β s) (P.transfer β' s) hcenter
  have hf := (SmoothSite.nisnevichPointFiberCocone X x F).w
    (SmoothSite.SmoothPointedEtaleNeighborhood.commonFst N M).op
  have hg := (SmoothSite.nisnevichPointFiberCocone X x F).w
    (SmoothSite.SmoothPointedEtaleNeighborhood.commonSnd N M).op
  change (F).map f.op ≫ (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op C) =
    (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op N) at hf
  change (F).map g.op ≫ (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op C) =
    (SmoothSite.nisnevichPointFiberCocone X x F).ι.app (op M) at hg
  have htransfer : P.transfer β s = (F).map f.op (P.transfer α s) := by
    dsimp only [β]
    rw [transfer_comp, ConcreteCategory.comp_apply]
    rfl
  have htransfer' : P.transfer β' s = (F).map g.op (P.transfer α' s) := by
    dsimp only [β']
    rw [transfer_comp, ConcreteCategory.comp_apply]
    rfl
  rw [htransfer, htransfer'] at hC
  exact (ConcreteCategory.congr_hom hf (P.transfer α s)).symm.trans
    (hC.trans (ConcreteCategory.congr_hom hg (P.transfer α' s)))

end AlgebraicGeometry.PresheafWithTransfers
