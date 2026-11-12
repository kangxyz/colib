/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Coproducts.PartialIdentity
public import Colib.AlgebraicGeometry.Correspondences.Graph.TargetPushforward

/-!
# Genuine correspondence projections for a finite clopen partition

The original diagonal cycle is partitioned by the actual images of a finite family of
clopen immersions. Its portions factor through the original graph correspondences.
The resulting projections satisfy the complete matrix identities in the original
correspondence category, including the empty partition of the empty scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Cor
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {I : Type u} [Fintype I]
  {W : SmoothSite (Spec (.of k))} {V : I → SmoothSite (Spec (.of k))}
  (q : ∀ i, V i ⟶ W)

/-- A finite clopen partition sums to the actual full diagonal cycle. -/
theorem sum_partialIdentity_eq_id [∀ i, IsClosedImmersion (q i).left]
    (hd : Pairwise fun i j => Disjoint (Set.range (q i).left) (Set.range (q j).left))
    (hc : ∀ x : W.left, ∃ i, x ∈ Set.range (q i).left) :
    ∑ i, partialIdentity k (q i) = 𝟙 (Cor.mk W) := by
  classical
  let := (finite_genericPoints k (Cor.mk W)).fintype
  rw [identity_eq_sum_diagonalPrime]
  unfold partialIdentity
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  obtain ⟨i, hi⟩ := hc s.val
  have hsi : closure {s.val} ⊆ Set.range (q i).left :=
    closure_minimal (Set.singleton_subset_iff.mpr hi) (q i).left.isClosedEmbedding.isClosed_range
  rw [Finset.sum_eq_single i]
  · simp only [ite_eq_left hsi]
  · intro j _ hji
    have hj : ¬ closure {s.val} ⊆ Set.range (q j).left := by
      intro hj
      exact Set.disjoint_left.mp (hd hji) (hj (subset_closure (Set.mem_singleton _))) hi
    simp only [ite_eq_right hj]
  · simp

/-- Actual inverse-clopen-graph cycles give a finite matrix decomposition of the identity. -/
theorem exists_clopenFamily_projections
    [∀ i, IsOpenImmersion (q i).left] [∀ i, IsClosedImmersion (q i).left]
    (hd : Pairwise fun i j => Disjoint (Set.range (q i).left) (Set.range (q j).left))
    (hc : ∀ x : W.left, ∃ i, x ∈ Set.range (q i).left) :
    ∃ p : ∀ i, Cor.mk W ⟶ Cor.mk (V i),
      (∀ i, (graphFunctor k).map (q i) ≫ p i = 𝟙 _) ∧
      (∀ i j, i ≠ j → (graphFunctor k).map (q i) ≫ p j = 0) ∧
      ∑ i, p i ≫ (graphFunctor k).map (q i) = 𝟙 (Cor.mk W) := by
  classical
  choose p hp using fun i => exists_partialIdentity_factorization k (q i)
  let g : ∀ i, Cor.mk (V i) ⟶ Cor.mk W := fun i => (graphFunctor k).map (q i)
  change ∀ i, p i ≫ g i = partialIdentity k (q i) at hp
  have hm (i) : Mono (g i) :=
    graph_map_mono_of_isClosedImmersion k _
  have htotal : ∑ i, p i ≫ g i = 𝟙 (Cor.mk W) := by
    simp_rw [hp]
    exact sum_partialIdentity_eq_id k q hd hc
  have hoff (i j) (hij : i ≠ j) : g i ≫ p j = 0 := by
    apply (cancel_mono (g j)).mp
    rw [Category.assoc, hp, zero_comp]
    exact graph_comp_partialIdentity_eq_zero k _ _ (hd hij)
  refine ⟨p, ?_, hoff, htotal⟩
  intro i
  change g i ≫ p i = 𝟙 (Cor.mk (V i))
  apply (cancel_mono (g i)).mp
  have hh := congrArg (fun a => g i ≫ a) htotal
  rw [Preadditive.comp_sum] at hh
  have hs : (∑ j, g i ≫
      (p j ≫ g j)) =
      g i ≫ (p i ≫ g i) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [← Category.assoc, hoff i j (Ne.symm hji), zero_comp]
    · simp
  simpa only [hs, Category.comp_id, Category.id_comp, Category.assoc] using hh

end AlgebraicGeometry.Cor
