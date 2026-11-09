/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeStableRepresentability
public import Colib.Topology.Prespectrum.StableEquivalence

/-!
# Stable invariance of the original reduced telescope

A strict map of sequential diagrams of levelwise T1 prespectra induces a stable
equivalence of the original reduced telescopes whenever each original stage map
is a stable equivalence. The proof uses actual stable representatives and
finite-stage detection of equality, without redefining stable homotopy groups
or imposing compatible inverse maps on the diagrams.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  (E' : ℕ → LoopPrespectrum.{u}) (f' : ∀ i, E' i ⟶ E' (i + 1))
  (a : ∀ i, E i ⟶ E' i) (ha : ∀ i, a i ≫ f' i = f i ≫ a (i + 1))

include ha in
/-- Strict diagram compatibility persists through every original finite transition. -/
theorem transition_naturality (i N : ℕ) (hi : i ≤ N) :
    transition E f i N hi ≫ a N = a i ≫ transition E' f' i N hi := by
  let α : Functor.ofSequence f ⟶ Functor.ofSequence f' :=
    NatTrans.ofSequence a (fun n ↦ by
      simp only [Functor.ofSequence_map_homOfLE_succ]
      exact (ha n).symm)
  exact α.naturality (homOfLE hi)

/-- Naturality on actual stable classes keeps the original stage inclusions. -/
theorem stableMap_inclusion_apply (d : ℤ) (i : ℕ) (x : stableHomotopyGroup (E i) d) :
    (stableHomotopyFunctor d).map (map E f E' f' a ha)
        ((stableHomotopyFunctor d).map (inclusion E f i) x) =
      (stableHomotopyFunctor d).map (inclusion E' f' i)
        ((stableHomotopyFunctor d).map (a i) x) := by
  have h := congrArg ((stableHomotopyFunctor d).map) (inclusion_map E f E' f' a ha i)
  simp only [Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h x

include ha in
/-- Naturality on actual stable classes keeps the original finite transition composites. -/
theorem stableMap_transition_apply (d : ℤ) (i N : ℕ) (hi : i ≤ N)
    (x : stableHomotopyGroup (E i) d) :
    (stableHomotopyFunctor d).map (a N)
        ((stableHomotopyFunctor d).map (transition E f i N hi) x) =
      (stableHomotopyFunctor d).map (transition E' f' i N hi)
        ((stableHomotopyFunctor d).map (a i) x) := by
  have h := congrArg ((stableHomotopyFunctor d).map) (transition_naturality E f E' f' a ha i N hi)
  simp only [Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h x

variable [∀ i k, T1Space ((E i).space k)] [∀ i k, T1Space ((E' i).space k)]

/-- Stagewise stable equivalences induce an original reduced-telescope stable equivalence. -/
theorem map_isStableEquivalence (h : ∀ i, IsStableEquivalence (a i)) :
    IsStableEquivalence (map E f E' f' a ha) := by
  intro d
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y hxy
    obtain ⟨i, x, rfl⟩ := exists_stable_representative E f d x
    obtain ⟨j, y, rfl⟩ := exists_stable_representative E f d y
    have h' := (stableMap_inclusion_apply E f E' f' a ha d i x).symm.trans
      (hxy.trans (stableMap_inclusion_apply E f E' f' a ha d j y))
    obtain ⟨N, hi, hj, hN⟩ := exists_eventual_stable_eq E' f' d
      ((stableHomotopyFunctor d).map (a i) x) ((stableHomotopyFunctor d).map (a j) y) h'
    have := h N d
    have hE : (stableHomotopyFunctor d).map (transition E f i N hi) x =
        (stableHomotopyFunctor d).map (transition E f j N hj) y := by
      apply (ConcreteCategory.bijective_of_isIso ((stableHomotopyFunctor d).map (a N))).1
      exact (stableMap_transition_apply E f E' f' a ha d i N hi x).trans
        (hN.trans (stableMap_transition_apply E f E' f' a ha d j N hj y).symm)
    exact (ConcreteCategory.congr_hom (inclusion_transition_stableMap E f hi d) x).trans
      ((congrArg ((stableHomotopyFunctor d).map (inclusion E f N)) hE).trans
        (ConcreteCategory.congr_hom (inclusion_transition_stableMap E f hj d) y).symm)
  · intro y
    obtain ⟨i, y, rfl⟩ := exists_stable_representative E' f' d y
    have := h i d
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso
      ((stableHomotopyFunctor d).map (a i))).2 y
    refine ⟨(stableHomotopyFunctor d).map (inclusion E f i) x, ?_⟩
    exact (stableMap_inclusion_apply E f E' f' a ha d i x).trans
      (congrArg ((stableHomotopyFunctor d).map (inclusion E' f' i)) hx)

end Topology.LoopPrespectrum.Telescope
