/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Coproducts.ClopenFamily
public import Colib.AlgebraicGeometry.Sites.Smooth.IntegralClopenComponents
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RadicialTorsion
public import Colib.AlgebraicGeometry.Sites.Smooth.FrobeniusFunctor

/-!
# Radicial torsion invariance on all original smooth objects

The original graph pullback is inverted on each actual integral clopen component by
its Bezout-scaled transposed graph. The component inverses are assembled with genuine
clopen projection correspondences. No connectedness, homotopy invariance or sheaf
condition is imposed on the original presheaf with transfers.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped BigOperators

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)

/-- Additivity applies to the finite sum of the actual signed cycles. -/
theorem transfer_sum {I : Type*} {X Y : Cor k} (s : Finset I) (a : I → (X ⟶ Y)) :
    transfer P (∑ i ∈ s, a i) = ∑ i ∈ s, transfer P (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, transfer_zero]
  | @insert i s hi h => simp only [Finset.sum_insert hi, transfer_add, h]

/-- Restriction to an actual finite clopen partition detects equality of section morphisms. -/
theorem clopenFamily_sections_jointly_monic {I : Type u} [Finite I]
    {W : SmoothSite (Spec (.of k))} {V : I → SmoothSite (Spec (.of k))}
    (q : ∀ i, V i ⟶ W)
    [∀ i, IsOpenImmersion (q i).left] [∀ i, IsClosedImmersion (q i).left]
    (hd : Pairwise fun i j => Disjoint (Set.range (q i).left) (Set.range (q j).left))
    (hc : ∀ x : W.left, ∃ i, x ∈ Set.range (q i).left)
    {T : AddCommGrpCat.{v}} (a b : T ⟶ sections P (Cor.mk W))
    (h : ∀ i, a ≫ ((toPresheaf k).obj P).map (q i).op =
      b ≫ ((toPresheaf k).obj P).map (q i).op) : a = b := by
  classical
  let := Fintype.ofFinite I
  obtain ⟨p, _, _, hp⟩ := Cor.exists_clopenFamily_projections k q hd hc
  let g : ∀ i, Cor.mk (V i) ⟶ Cor.mk W := fun i => (Cor.graphFunctor k).map (q i)
  change ∑ i, p i ≫ g i = 𝟙 (Cor.mk W) at hp
  have ht : ∑ i, transfer P (g i) ≫ transfer P (p i) = 𝟙 (sections P (Cor.mk W)) := by
    rw [← transfer_id P (Cor.mk W), ← hp, transfer_sum]
    simp only [transfer_comp]
  calc
    a = a ≫ (∑ i, transfer P (g i) ≫ transfer P (p i)) := by rw [ht, Category.comp_id]
    _ = b ≫ (∑ i, transfer P (g i) ≫ transfer P (p i)) := by
      simp only [Preadditive.comp_sum, ← Category.assoc]
      exact Finset.sum_congr rfl fun i _ => congrArg (fun f => f ≫ transfer P (p i)) (h i)
    _ = b := by rw [ht, Category.comp_id]

/-- Actual clopen partitions glue inverse maps on the original section groups. -/
def clopenFamilyGraphIso {I : Type u} [Fintype I]
    {X Y : SmoothSite (Spec (.of k))} (q : X ⟶ Y)
    {U V : I → SmoothSite (Spec (.of k))}
    (a : ∀ i, U i ⟶ X) (b : ∀ i, V i ⟶ Y) (r : ∀ i, U i ⟶ V i)
    [∀ i, IsOpenImmersion (a i).left] [∀ i, IsClosedImmersion (a i).left]
    [∀ i, IsOpenImmersion (b i).left] [∀ i, IsClosedImmersion (b i).left]
    (ha : Pairwise fun i j => Disjoint (Set.range (a i).left) (Set.range (a j).left))
    (hca : ∀ x : X.left, ∃ i, x ∈ Set.range (a i).left)
    (hb : Pairwise fun i j => Disjoint (Set.range (b i).left) (Set.range (b j).left))
    (hcb : ∀ y : Y.left, ∃ i, y ∈ Set.range (b i).left)
    (hr : ∀ i, r i ≫ b i = a i ≫ q)
    (e : ∀ i, sections P (Cor.mk (V i)) ≅ sections P (Cor.mk (U i)))
    (he : ∀ i, (e i).hom = ((toPresheaf k).obj P).map (r i).op) :
    sections P (Cor.mk Y) ≅ sections P (Cor.mk X) := by
  classical
  let F := (toPresheaf k).obj P
  let g : sections P (Cor.mk Y) ⟶ sections P (Cor.mk X) := F.map q.op
  let A : ∀ i, sections P (Cor.mk X) ⟶ sections P (Cor.mk (U i)) :=
    fun i => F.map (a i).op
  let B : ∀ i, sections P (Cor.mk Y) ⟶ sections P (Cor.mk (V i)) :=
    fun i => F.map (b i).op
  have hs (i) : g ≫ A i = B i ≫ (e i).hom := by
    rw [he]
    change F.map q.op ≫ F.map (a i).op = F.map (b i).op ≫ F.map (r i).op
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg (fun f : U i ⟶ Y => F.map f.op) (hr i).symm
  let p := (Cor.exists_clopenFamily_projections k b hb hcb).choose
  obtain ⟨hp, hp', hpt⟩ := (Cor.exists_clopenFamily_projections k b hb hcb).choose_spec
  let G : ∀ i, Cor.mk (V i) ⟶ Cor.mk Y := fun i => (Cor.graphFunctor k).map (b i)
  change ∀ i, G i ≫ p i = 𝟙 (Cor.mk (V i)) at hp
  change ∀ i j, i ≠ j → G i ≫ p j = 0 at hp'
  change ∑ i, p i ≫ G i = 𝟙 (Cor.mk Y) at hpt
  let J : ∀ i, sections P (Cor.mk (V i)) ⟶ sections P (Cor.mk Y) := fun i => transfer P (p i)
  have hJB (i) : J i ≫ B i = 𝟙 _ := by
    change transfer P (p i) ≫ transfer P (G i) = _
    rw [← transfer_comp, hp, transfer_id]
  have hJB' (i j) (hij : i ≠ j) : J i ≫ B j = 0 := by
    change transfer P (p i) ≫ transfer P (G j) = _
    rw [← transfer_comp, hp' j i (Ne.symm hij), transfer_zero]
  have hBJ : ∑ i, B i ≫ J i = 𝟙 (sections P (Cor.mk Y)) := by
    rw [← transfer_id P (Cor.mk Y), ← hpt, transfer_sum]
    simp only [transfer_comp]
    rfl
  let inv : sections P (Cor.mk X) ⟶ sections P (Cor.mk Y) :=
    ∑ i, A i ≫ (e i).inv ≫ J i
  have hinvB (i) : inv ≫ B i = A i ≫ (e i).inv := by
    dsimp only [inv]
    rw [Preadditive.sum_comp]
    rw [Finset.sum_eq_single i]
    · rw [Category.assoc, Category.assoc, hJB, Category.comp_id]
    · intro j _ hji
      rw [Category.assoc, Category.assoc, hJB' j i hji, comp_zero, comp_zero]
    · simp
  refine { hom := g, inv := inv, hom_inv_id := ?_, inv_hom_id := ?_ }
  · change g ≫ (∑ i, A i ≫ (e i).inv ≫ J i) = _
    rw [Preadditive.comp_sum]
    calc
      _ = ∑ i, B i ≫ J i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Category.assoc, hs, Category.assoc, Iso.hom_inv_id_assoc]
      _ = _ := hBJ
  · apply clopenFamily_sections_jointly_monic P a ha hca
    intro i
    change (inv ≫ g) ≫ A i = 𝟙 _ ≫ A i
    rw [Category.assoc, hs, ← Category.assoc, hinvB, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- For arbitrary original smooth objects, prime-to-characteristic torsion sections are
invariant under the original finite flat universal homeomorphism. The inverse is the sum
of the actual integral-component Bezout transfer inverses and clopen projections. -/
@[colib_tag "COL-1103", colib_ref "MVW2006"
  "Lecture 1, Exercise 1.11, printed p. 6; Lecture 2, Definition 2.1, printed p. 13"
  "adaptation" "actual full-degree transfer inverses glued over finite clopen components"]
def radicialGraphIsoOfComponents {X Y : SmoothSite (Spec (.of k))} (q : X ⟶ Y)
    [IsFinite q.left] [Flat q.left] [UniversalHomeomorphism q.left]
    (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    sections P (Cor.mk Y) ≅ sections P (Cor.mk X) := by
  letI : Finite (irreducibleComponents Y.left) := finite_componentOpenCover_index k Y
  letI := Fintype.ofFinite (irreducibleComponents Y.left)
  exact clopenFamilyGraphIso P q
    (integralComponentPullbackι k q) (integralComponentι k Y) (integralComponentMap k q)
    (pairwiseDisjoint_integralComponentPullbackι k q) (integralComponentPullbackι_covers k q)
    (pairwiseDisjoint_integralComponentι k Y) (integralComponentι_covers k Y)
    (integralComponentMap_comm k q)
    (fun Z => radicialGraphIso P (integralComponentMap k q Z) n hn
      (hP (integralComponentPullback k q Z)) (hP (integralComponent k Y Z)))
    (fun Z => radicialGraphIso_hom P (integralComponentMap k q Z) n hn _ _)

/-- The isomorphism retains precisely the original graph pullback as its forward map. -/
@[simp]
theorem radicialGraphIsoOfComponents_hom {X Y : SmoothSite (Spec (.of k))} (q : X ⟶ Y)
    [IsFinite q.left] [Flat q.left] [UniversalHomeomorphism q.left]
    (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    (radicialGraphIsoOfComponents P q n hn hP).hom =
      ((toPresheaf k).obj P).map q.op := rfl

/-- The inverse is literally a finite sum of original component restrictions,
full-degree Bezout transpose transfers, and actual clopen projection transfers. -/
theorem radicialGraphIsoOfComponents_inv {X Y : SmoothSite (Spec (.of k))} (q : X ⟶ Y)
    [IsFinite q.left] [Flat q.left] [UniversalHomeomorphism q.left]
    (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    letI : Finite (irreducibleComponents Y.left) := finite_componentOpenCover_index k Y
    letI := Fintype.ofFinite (irreducibleComponents Y.left)
    let π := (Cor.exists_clopenFamily_projections k (integralComponentι k Y)
      (pairwiseDisjoint_integralComponentι k Y) (integralComponentι_covers k Y)).choose
    (radicialGraphIsoOfComponents P q n hn hP).inv =
      ∑ Z, ((toPresheaf k).obj P).map (integralComponentPullbackι k q Z).op ≫
        (Nat.gcdA ((integralComponentMap k q Z).left.residueDegree
          (genericPoint (integralComponentPullback k q Z).left)) n •
          transfer P (Cor.finiteFlatTranspose k (integralComponentMap k q Z))) ≫
        transfer P (π Z) := rfl

/-- No integrality or connectedness is required for the original restriction map. -/
@[colib_tag "COL-1103"]
theorem isIso_toPresheaf_map_of_universalHomeomorphism
    {X Y : SmoothSite (Spec (.of k))} (q : X ⟶ Y)
    [IsFinite q.left] [Flat q.left] [UniversalHomeomorphism q.left]
    (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    IsIso (((toPresheaf k).obj P).map q.op) :=
  (radicialGraphIsoOfComponents P q n hn hP).isIso_hom

/-- The actual relative Frobenius acts invertibly on all original smooth objects,
including empty and disconnected objects, over an arbitrary field of positive characteristic. -/
@[colib_tag "COL-1103"]
def relativeFrobeniusIsoOfComponents (p : ℕ) [Fact p.Prime]
    (hk : Stacks.Frobenius.IsInCharacteristic (Spec (.of k)) p)
    (X : SmoothSite (Spec (.of k))) (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    sections P (Cor.mk (SmoothSite.frobeniusTwist p hk X)) ≅ sections P (Cor.mk X) :=
  radicialGraphIsoOfComponents P (SmoothSite.relativeFrobenius p hk X) n hn hP

@[simp]
theorem relativeFrobeniusIsoOfComponents_hom (p : ℕ) [Fact p.Prime]
    (hk : Stacks.Frobenius.IsInCharacteristic (Spec (.of k)) p)
    (X : SmoothSite (Spec (.of k))) (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    (relativeFrobeniusIsoOfComponents P p hk X n hn hP).hom =
      ((toPresheaf k).obj P).map (SmoothSite.relativeFrobenius p hk X).op := rfl

/-- The actual Frobenius pullbacks form a natural isomorphism of the original underlying
ordinary presheaf, without an integral-object restriction or a replacement category. -/
@[colib_tag "COL-1103"]
def relativeFrobeniusPresheafIso (p : ℕ) [Fact p.Prime]
    (hk : Stacks.Frobenius.IsInCharacteristic (Spec (.of k)) p)
    (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    (frobeniusTwistFunctor p hk).op ⋙ (toPresheaf k).obj P ≅ (toPresheaf k).obj P := by
  refine NatIso.ofComponents
    (fun X => relativeFrobeniusIsoOfComponents P p hk X.unop n hn hP) ?_
  intro X Y f
  let F := (toPresheaf k).obj P
  let T := frobeniusTwistFunctor p hk
  let η : 𝟭 _ ⟶ T := relativeFrobeniusNatTrans p hk
  change F.map (T.map f.unop).op ≫ F.map (η.app Y.unop).op =
    F.map (η.app X.unop).op ≫ F.map f
  rw [← F.map_comp, ← F.map_comp]
  exact congrArg (fun a : Y.unop ⟶ T.obj X.unop => F.map a.op)
    (η.naturality f.unop).symm

@[simp]
theorem relativeFrobeniusPresheafIso_hom_app (p : ℕ) [Fact p.Prime]
    (hk : Stacks.Frobenius.IsInCharacteristic (Spec (.of k)) p)
    (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ))
    (X : (SmoothSite (Spec (.of k)))ᵒᵖ) :
    (relativeFrobeniusPresheafIso P p hk n hn hP).hom.app X =
      ((toPresheaf k).obj P).map (SmoothSite.relativeFrobenius p hk X.unop).op := rfl

end AlgebraicGeometry.PresheafWithTransfers
