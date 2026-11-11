/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Points.ChosenGeneratorLift
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Sections
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction

/-!
# Genuine signed transfer locality at arbitrary scheme points

Choose actual zero representatives at the target points of the original
finite support fiber and apply the native chosen-center family factorization.
The actual presheaf maps carry its graph equality to a zero restriction.
Native finite signed decomposition then gives locality for any correspondence.
No closedness, positivity, or extra sheaf condition is assumed.

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Sheaf/Germs/ArbitraryPointLocality.lean`,
blob `852788ab9620e1e9a2502bc7014af2017014d36e`, and the finite-sum calculation
in `Motivic/Transfers/Sheaf/Germs/FiniteSupportLocality.lean`,
blob `a4b6aafecef33f7e082141ffd8ea3a502c4da6f8`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Chow
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u v w

namespace AlgebraicGeometry.PresheafWithTransfers

open Scheme

variable (k : Type u) [Field k]
  (P : PresheafWithTransfers.{max (u + 1) v} k)
  {X Y : SmoothSite (Spec (.of k))}

private theorem transfer_finset_sum_apply {I : Type w} (E : Finset I)
    (α : I → (Cor.mk X ⟶ Cor.mk Y)) (s : P.sections (Cor.mk Y)) :
    P.transfer (∑ i ∈ E, α i) s = ∑ i ∈ E, P.transfer (α i) s := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | @insert i E hi h =>
    simp only [Finset.sum_insert hi, transfer_add, AddCommGrpCat.hom_add_apply, h]

/-- A signed prime transfers a section to zero in the original source germ
when every target germ met by its actual source fiber is zero. -/
theorem generator_transfer_germ_eq_zero_at_point
    (a : pullback (C := Scheme) X.hom Y.hom)
    (ha : IsFiniteCorrespondencePoint X.hom Y.hom a) (c : ℤ)
    (x : X.left) (s : P.sections (Cor.mk Y))
    (hs : ∀ z : (integralComponentAt a).subscheme,
      ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom) z = x →
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) Y
        (((integralComponentAt a).subschemeι ≫ pullback.snd X.hom Y.hom) z) s = 0) :
    SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x
      (P.transfer (singleFiniteCorrespondence X.hom Y.hom a ha c) s) = 0 := by
  classical
  let p := (integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom
  let target := (integralComponentAt a).subschemeι ≫ pullback.snd X.hom Y.hom
  let I := {z : (integralComponentAt a).subscheme // p z = x}
  have hrep (z : I) := (SmoothSite.sectionToNisnevichPoint_eq_zero_iff.{u, v}
    ((toPresheaf k).obj P) (X := Y) (x := target z.val) s).mp (hs z.val z.property)
  choose R hR using hrep
  let V (z : I) := (SmoothSite.nisnevichNeighborhoodFunctor Y (target z.val)).obj (R z)
  let q (z : I) : V z ⟶ Y := (R z).toBase
  have : ∀ z, Etale (q z).left := by intro z; dsimp only [q]; infer_instance
  obtain ⟨N, n, label, β, hβ, _⟩ :=
    Cor.exists_pointed_graph_family_factorization_at_chosen_points k a ha c x V q
      (fun z => (R z).center) (by
        intro z hz
        exact ⟨⟨z, hz⟩, (R ⟨z, hz⟩).toBase_center, inferInstance⟩)
  apply (SmoothSite.sectionToNisnevichPoint_eq_zero_iff _ _).mpr
  refine ⟨N, ?_⟩
  change (P.transfer (singleFiniteCorrespondence X.hom Y.hom a ha c) ≫
    P.transfer ((Cor.graphFunctor k).map N.toBase)) s = 0
  rw [← transfer_comp, ← hβ]
  erw [transfer_finset_sum_apply k P Finset.univ
    (fun j : Fin n => β j ≫ (Cor.graphFunctor k).map (q (label j))) s]
  apply Finset.sum_eq_zero
  intro j _
  rw [transfer_comp, ConcreteCategory.comp_apply]
  erw [hR (label j), map_zero]

/-- Locality for every signed native correspondence, including zero and all
integer cancellations, at every original source point. -/
theorem transfer_germ_eq_zero_at_point
    (α : Cor.mk X ⟶ Cor.mk Y) (x : X.left) (s : P.sections (Cor.mk Y))
    (hs : ∀ a, α.val a ≠ 0 → ∀ z : (integralComponentAt a).subscheme,
      ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom) z = x →
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) Y
        (((integralComponentAt a).subschemeι ≫ pullback.snd X.hom Y.hom) z) s = 0) :
    SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x (P.transfer α s) = 0 := by
  classical
  let ι := SmoothSite.sectionToNisnevichPoint.{u, v} ((toPresheaf k).obj P) X x
  let L : (Cor.mk X ⟶ Cor.mk Y) →+
      (SmoothSite.nisnevichPointFiberCocone X x ((toPresheaf k).obj P)).pt :=
    { toFun := fun γ => ι (P.transfer γ s)
      map_zero' := by simp
      map_add' := fun γ δ => by
        simp only [transfer_add, AddCommGrpCat.hom_add_apply, map_add] }
  change L α = 0
  rw [finiteCorrespondence_eq_sum_signedSingles X.hom Y.hom α, map_sum]
  apply Finset.sum_eq_zero
  intro a _
  apply generator_transfer_germ_eq_zero_at_point k P a.val _ (α.val a.val) x s
  apply hs a.val
  simpa only [Set.Finite.mem_toFinset, support, Function.mem_support] using a.property

/-- Equal actual target germs give equal original source germs after signed transfer. -/
theorem transfer_germ_eq_at_point_of_eq_on_support
    (α : Cor.mk X ⟶ Cor.mk Y) (x : X.left) (s t : P.sections (Cor.mk Y))
    (hst : ∀ a, α.val a ≠ 0 → ∀ z : (integralComponentAt a).subscheme,
      ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom) z = x →
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) Y
        (((integralComponentAt a).subschemeι ≫ pullback.snd X.hom Y.hom) z) s =
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) Y
        (((integralComponentAt a).subschemeι ≫ pullback.snd X.hom Y.hom) z) t) :
    SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x (P.transfer α s) =
      SmoothSite.sectionToNisnevichPoint ((toPresheaf k).obj P) X x (P.transfer α t) := by
  have hz := transfer_germ_eq_zero_at_point k P α x (s - t) (by
    intro a ha z hx
    rw [map_sub, hst a ha z hx, sub_self])
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

end AlgebraicGeometry.PresheafWithTransfers
