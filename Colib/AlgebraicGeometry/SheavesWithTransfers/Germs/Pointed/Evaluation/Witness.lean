/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Germs.Pointed.Evaluation.Signed
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Germs.Pointed.Lifts.CorrespondenceAlgebra

/-! # Actual finite witnesses compute the signed correspondence evaluation -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Chow
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable (k : Type u) [Field k] (P : PresheafWithTransfers.{u + 1} k)
  (hP : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k))) ((toPresheaf k).obj P))
  {X Y : SmoothSite (Spec (.of k))}

/-- A concrete witness whose original-colimit value is the signed evaluation. -/
def HasComputingPointedGermLift (δ : Cor.mk X ⟶ Cor.mk Y) (x : X.left)
    (a : ∀ y : Y.left,
      (SmoothSite.nisnevichPointFiberCocone Y y ((toPresheaf k).obj P)).pt) : Prop :=
  ∃ L : PointedGermLiftWitness k P δ x a,
    L.value k P = correspondenceGermHom k P hP x δ a

namespace HasComputingPointedGermLift
open _root_.AlgebraicGeometry.Scheme
variable (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y ((toPresheaf k).obj P)).pt)
include a

theorem zero : HasComputingPointedGermLift k P hP (0 : Cor.mk X ⟶ Cor.mk Y) x a := by
  refine ⟨PointedGermLiftWitness.zero k P x a, ?_⟩
  rw [PointedGermLiftWitness.value_zero, map_zero, AddMonoidHom.zero_apply]

theorem add (δ ε : Cor.mk X ⟶ Cor.mk Y)
    (hδ : HasComputingPointedGermLift k P hP δ x a)
    (hε : HasComputingPointedGermLift k P hP ε x a) :
    HasComputingPointedGermLift k P hP (δ + ε) x a := by
  obtain ⟨L, hL⟩ := hδ
  obtain ⟨M, hM⟩ := hε
  refine ⟨L.add k P M, ?_⟩
  rw [PointedGermLiftWitness.value_add, hL, hM, map_add, AddMonoidHom.add_apply]

theorem neg (δ : Cor.mk X ⟶ Cor.mk Y)
    (hδ : HasComputingPointedGermLift k P hP δ x a) :
    HasComputingPointedGermLift k P hP (-δ) x a := by
  obtain ⟨L, hL⟩ := hδ
  refine ⟨L.neg k P, ?_⟩
  rw [PointedGermLiftWitness.value_neg, hL, map_neg, AddMonoidHom.neg_apply]

theorem cycle (A : pullback (C := Scheme) X.hom Y.hom)
    (hA : IsFiniteCorrespondencePoint X.hom Y.hom A) :
    HasComputingPointedGermLift k P hP (show Cor.mk X ⟶ Cor.mk Y from (singleFiniteCorrespondence X.hom Y.hom A hA 1)) x a := by
  obtain ⟨L⟩ := exists_pointedGermLiftWitness k P A hA 1 x a
  refine ⟨L, ?_⟩
  rw [correspondenceGermHom_cycle]
  exact (generatorGermEvaluation_eq_of_witness k P hP A hA x a L).symm

theorem zsmul (δ : Cor.mk X ⟶ Cor.mk Y)
    (hδ : HasComputingPointedGermLift k P hP δ x a) (m : ℤ) :
    HasComputingPointedGermLift k P hP (m • δ) x a := by
  induction m using Int.induction_on with
  | zero => simpa only [zero_zsmul] using zero k P hP x a
  | succ n ih =>
    simpa only [add_zsmul, one_zsmul] using
      add k P hP x a ((n : ℤ) • δ) δ ih hδ
  | pred n ih =>
    simpa only [sub_zsmul, one_zsmul, sub_eq_add_neg] using
      add k P hP x a ((-(n : ℤ)) • δ) (-δ) ih (neg k P hP x a δ hδ)

theorem single (A : pullback (C := Scheme) X.hom Y.hom)
    (hA : IsFiniteCorrespondencePoint X.hom Y.hom A) (m : ℤ) :
    HasComputingPointedGermLift k P hP
      (singleFiniteCorrespondence X.hom Y.hom A hA m) x a := by
  rw [singleFiniteCorrespondence_eq_zsmul]
  exact zsmul k P hP x a _ (cycle k P hP x a A hA) m

end HasComputingPointedGermLift

/-- Every signed correspondence admits a genuine finite witness computing its
signed evaluation. The construction uses actual common sources and finite unions. -/
theorem exists_signed_pointedGermLiftWitness
    (δ : Cor.mk X ⟶ Cor.mk Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y ((toPresheaf k).obj P)).pt) :
    ∃ L : PointedGermLiftWitness k P δ x a,
      L.value k P = correspondenceGermHom k P hP x δ a := by
  classical
  change HasComputingPointedGermLift k P hP δ x a
  have hsum {ι : Type*} (s : Finset ι) (d : ι → (Cor.mk X ⟶ Cor.mk Y))
      (hd : ∀ i ∈ s, HasComputingPointedGermLift k P hP (d i) x a) :
      HasComputingPointedGermLift k P hP (∑ i ∈ s, d i) x a := by
    induction s using Finset.induction_on with
    | empty => simpa using HasComputingPointedGermLift.zero k P hP x a
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact HasComputingPointedGermLift.add k P hP x a _ _
        (hd i (Finset.mem_insert_self i s))
        (ih (fun j hj => hd j (Finset.mem_insert_of_mem hj)))
  rw [finiteCorrespondence_eq_sum_signedSingles X.hom Y.hom δ]
  exact hsum Finset.univ _ (fun A _ =>
    HasComputingPointedGermLift.single k P hP x a A.val _ _)

/-- No choice of actual source, targets, branches, or representatives changes the
signed evaluation in the original source-point colimit. -/
theorem correspondenceGermHom_eq_of_witness
    (δ : Cor.mk X ⟶ Cor.mk Y) (x : X.left)
    (a : ∀ y : Y.left, (SmoothSite.nisnevichPointFiberCocone Y y ((toPresheaf k).obj P)).pt)
    (L : PointedGermLiftWitness k P δ x a) :
    correspondenceGermHom k P hP x δ a = L.value k P := by
  obtain ⟨M, hM⟩ := exists_signed_pointedGermLiftWitness k P hP δ x a
  exact hM.symm.trans (M.value_eq k P hP L)

end AlgebraicGeometry.PresheafWithTransfers

