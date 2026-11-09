/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.GeneratorLift

/-!
# Clopen portions of the actual correspondence identity

The full diagonal is split by its actual generic components. A portion whose
support lies in an open target image factors through the genuine graph of that
open immersion, by lifting the entire integral support. Disjoint images give
empty actual incidence schemes and hence zero original Tor correspondences.

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Coproducts/Binary.lean`,
blob `993ffbf915b22adc8cec07f62ccbc3e35049608e`, partial-identity section.
This uses the native generic-point cycle subgroup rather than the original
custom integral-subscheme Finsupp realization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Cor
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

/-- A single genuine diagonal component, indexed by its actual generic point. -/
def diagonalPrime (W : SmoothSite (Spec (.of k))) (s : genericPoints W.left) :
    Cor.mk W ⟶ Cor.mk W :=
  singleFiniteCorrespondence W.hom W.hom
    (correspondenceGraphMap W.hom W.hom (𝟙 W.left) (Category.id_comp _) s.val)
    (isFiniteCorrespondencePoint_graphMap W.hom W.hom (𝟙 W.left)
      (Category.id_comp _) s) 1

/-- The native full identity is the sum of exactly these actual diagonal primes. -/
theorem identity_eq_sum_diagonalPrime (W : SmoothSite (Spec (.of k))) :
    𝟙 (Cor.mk W) =
      let := (finite_genericPoints k (Cor.mk W)).fintype
      ∑ s : genericPoints W.left, diagonalPrime k W s := by
  exact graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence W.hom W.hom
    (𝟙 W.left) (Category.id_comp _) (finite_genericPoints k (Cor.mk W))

/-- The actual diagonal components whose whole support lies in the indicated image. -/
def partialIdentity {V W : SmoothSite (Spec (.of k))} (q : V ⟶ W) :
    Cor.mk W ⟶ Cor.mk W := by
  classical
  let := (finite_genericPoints k (Cor.mk W)).fintype
  exact ∑ s : genericPoints W.left,
    if closure {s.val} ⊆ Set.range q.left then diagonalPrime k W s else 0

/-- The indicated diagonal portion factors through an actual open-immersion graph. -/
theorem exists_partialIdentity_factorization
    {V W : SmoothSite (Spec (.of k))} (q : V ⟶ W) [IsOpenImmersion q.left] :
    ∃ p : Cor.mk W ⟶ Cor.mk V, p ≫ (graphFunctor k).map q = partialIdentity k q := by
  classical
  let := (finite_genericPoints k (Cor.mk W)).fintype
  have hlift (s : genericPoints W.left) (hs : closure {s.val} ⊆ Set.range q.left) :
      ∃ p : Cor.mk W ⟶ Cor.mk V, p ≫ (graphFunctor k).map q = diagonalPrime k W s := by
    apply exists_graph_factorization_of_range_subset k _ _ q
    have hd := integralComponentAt_graphMap_snd W.hom W.hom (𝟙 W.left)
      (Category.id_comp _) s.val
    have hid := hd.trans ((Category.assoc _ _ _).symm.trans (Category.comp_id _))
    rw [hid, range_integralComponentAt_graphMap_fst]
    exact hs
  choose p hp using hlift
  let Γq : Cor.mk V ⟶ Cor.mk W := (graphFunctor k).map q
  change ∀ s hs, p s hs ≫ Γq = diagonalPrime k W s at hp
  refine ⟨∑ s : genericPoints W.left,
    if hs : closure {s.val} ⊆ Set.range q.left then p s hs else 0, ?_⟩
  change (∑ s : genericPoints W.left,
    if hs : closure {s.val} ⊆ Set.range q.left then p s hs else 0) ≫ Γq = _
  rw [Preadditive.sum_comp]
  unfold partialIdentity
  apply Finset.sum_congr rfl
  intro s _
  split_ifs with hs
  · exact hp s hs
  · simp

/-- Disjoint actual images cannot meet in the original graph-diagonal incidence scheme. -/
theorem graph_comp_partialIdentity_eq_zero
    {U V W : SmoothSite (Spec (.of k))} (q : U ⟶ W) (r : V ⟶ W)
    (h : Disjoint (Set.range q.left) (Set.range r.left)) :
    (graphFunctor k).map q ≫ partialIdentity k r = 0 := by
  classical
  let := (finite_genericPoints k (Cor.mk W)).fintype
  let := (finite_genericPoints k (Cor.mk U)).fintype
  let Γq : Cor.mk U ⟶ Cor.mk W := (graphFunctor k).map q
  change Γq ≫ partialIdentity k r = 0
  unfold partialIdentity
  rw [Preadditive.comp_sum]
  apply Finset.sum_eq_zero
  intro s _
  split_ifs with hs
  · change incidenceTorPairing U.hom W.hom W.hom
      (graphCorrespondenceOfComponents U.hom W.hom q.left
        (MorphismProperty.Over.w q) (finite_genericPoints k (Cor.mk U)))
      (diagonalPrime k W s) = 0
    rw [graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence]
    simp only [map_sum, AddMonoidHom.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro t _
    let a := correspondenceGraphMap U.hom W.hom q.left (MorphismProperty.Over.w q) t.val
    let b := correspondenceGraphMap W.hom W.hom (𝟙 W.left) (Category.id_comp _) s.val
    have ha : IsFiniteCorrespondencePoint U.hom W.hom a :=
      isFiniteCorrespondencePoint_graphMap U.hom W.hom q.left (MorphismProperty.Over.w q) t
    have hb : IsFiniteCorrespondencePoint W.hom W.hom b :=
      isFiniteCorrespondencePoint_graphMap W.hom W.hom (𝟙 W.left) (Category.id_comp _) s
    change incidenceTorPairing U.hom W.hom W.hom
      (singleFiniteCorrespondence U.hom W.hom a ha 1)
      (singleFiniteCorrespondence W.hom W.hom b hb 1) = 0
    rw [incidenceTorPairing_single_one]
    let A := correspondenceIncidence U.hom W.hom W.hom a b
    have : IsEmpty A := ⟨fun x => by
      let x₁ := pullback.fst
        ((integralComponentAt a).subschemeι ≫ pullback.snd U.hom W.hom)
        ((integralComponentAt b).subschemeι ≫ pullback.fst W.hom W.hom) x
      let x₂ := pullback.snd
        ((integralComponentAt a).subschemeι ≫ pullback.snd U.hom W.hom)
        ((integralComponentAt b).subschemeι ≫ pullback.fst W.hom W.hom) x
      have hxq : ((integralComponentAt a).subschemeι ≫ pullback.snd U.hom W.hom) x₁ ∈
          Set.range q.left := by
        rw [integralComponentAt_graphMap_snd U.hom W.hom q.left
          (MorphismProperty.Over.w q) t.val]
        exact Set.mem_range_self _
      have hxr : ((integralComponentAt b).subschemeι ≫ pullback.fst W.hom W.hom) x₂ ∈
          Set.range r.left := by
        apply hs
        rw [← range_integralComponentAt_graphMap_fst W.hom W.hom (𝟙 W.left)
          (Category.id_comp _) s.val]
        exact Set.mem_range_self _
      have heq : ((integralComponentAt a).subschemeι ≫ pullback.snd U.hom W.hom) x₁ =
          ((integralComponentAt b).subschemeι ≫ pullback.fst W.hom W.hom) x₂ :=
        congrArg (fun f => f x) (pullback.condition (f :=
          (integralComponentAt a).subschemeι ≫ pullback.snd U.hom W.hom)
          (g := (integralComponentAt b).subschemeι ≫ pullback.fst W.hom W.hom))
      exact Set.disjoint_left.mp h (heq ▸ hxq) hxr⟩
    apply incidenceTorCorrespondence_eq_zero_of_genericPoints_eq_empty
    exact Set.eq_empty_iff_forall_notMem.mpr fun z _ => isEmptyElim z
  · simp

end AlgebraicGeometry.Cor
