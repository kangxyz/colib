/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeEventualHomotopy
public import Colib.Topology.Prespectrum.StableHomotopy
public import Mathlib.Algebra.Category.Grp.AB

/-!
# Finite representatives in the original stable groups of a telescope

For levelwise T1 stage prespectra, every class in the actual integer-graded
stable homotopy group of the original reduced telescope comes from an original
stage prespectrum. Equality is detected after a finite original transition.
The stable groups and their structure-induced suspension maps are unchanged.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  [∀ i k, T1Space ((E i).space k)]

/-- An original stable-stage group of the telescope is covered by original telescope-stage maps. -/
theorem exists_stableStage_representative (d : ℤ) (n : ℕ)
    (a : (stableSystem (prespectrum E f) d).obj n) :
    ∃ i : ℕ, ∃ b : (stableSystem (E i) d).obj n,
      (stableSystemMap (inclusion E f i) d).app n b = a := by
  obtain ⟨i, b, hb⟩ := exists_homotopyGroup_representative E f
    ((-d).toNat + n + 2) (d.toNat + n + 2) a.toMul
  exact ⟨i, Additive.ofMul b, congrArg Additive.ofMul hb⟩

/-- Equality in an original stable-stage group is detected in a finite telescope stage. -/
theorem exists_eventual_stableStage_eq (d : ℤ) (n : ℕ) {i j : ℕ}
    (a : (stableSystem (E i) d).obj n) (b : (stableSystem (E j) d).obj n)
    (hab : (stableSystemMap (inclusion E f i) d).app n a =
      (stableSystemMap (inclusion E f j) d).app n b) :
    ∃ N : ℕ, ∃ hi : i ≤ N, ∃ hj : j ≤ N,
      (stableSystemMap (transition E f i N hi) d).app n a =
        (stableSystemMap (transition E f j N hj) d).app n b := by
  obtain ⟨N, hi, hj, hN⟩ := exists_eventual_homotopyGroup_eq E f
    ((-d).toNat + n + 2) (d.toNat + n + 2) a.toMul b.toMul (congrArg Additive.toMul hab)
  exact ⟨N, hi, hj, congrArg Additive.ofMul hN⟩

/-- Every original integer-graded stable class of the telescope comes from a stage prespectrum. -/
theorem exists_stable_representative (d : ℤ) (a : stableHomotopyGroup (prespectrum E f) d) :
    ∃ i : ℕ, ∃ b : stableHomotopyGroup (E i) d,
      (stableHomotopyFunctor d).map (inclusion E f i) b = a := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨n, a, rfl⟩ := Concrete.colimit_exists_rep (stableSystem (prespectrum E f) d) a
  obtain ⟨i, b, hb⟩ := exists_stableStage_representative E f d n a
  refine ⟨i, stableHomotopyι (E i) d n b, ?_⟩
  exact (ConcreteCategory.congr_hom (stableHomotopyι_naturality (inclusion E f i) d n) b).trans
    (congrArg (stableHomotopyι (prespectrum E f) d n) hb)

/-- Equality of original stable images is detected after finitely many original transitions. -/
theorem exists_eventual_stable_eq (d : ℤ) {i j : ℕ}
    (a : stableHomotopyGroup (E i) d) (b : stableHomotopyGroup (E j) d)
    (hab : (stableHomotopyFunctor d).map (inclusion E f i) a =
      (stableHomotopyFunctor d).map (inclusion E f j) b) :
    ∃ N : ℕ, ∃ hi : i ≤ N, ∃ hj : j ≤ N,
      (stableHomotopyFunctor d).map (transition E f i N hi) a =
        (stableHomotopyFunctor d).map (transition E f j N hj) b := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨m, a, rfl⟩ := Concrete.colimit_exists_rep (stableSystem (E i) d) a
  obtain ⟨n, b, rfl⟩ := Concrete.colimit_exists_rep (stableSystem (E j) d) b
  change (stableHomotopyFunctor d).map (inclusion E f i) (stableHomotopyι (E i) d m a) =
    (stableHomotopyFunctor d).map (inclusion E f j) (stableHomotopyι (E j) d n b) at hab
  have hab' :=
    (ConcreteCategory.congr_hom (stableHomotopyι_naturality (inclusion E f i) d m) a).symm.trans
      (hab.trans
        (ConcreteCategory.congr_hom (stableHomotopyι_naturality (inclusion E f j) d n) b))
  obtain ⟨l, hm, hn, h⟩ := Concrete.colimit_exists_of_rep_eq (stableSystem (prespectrum E f) d)
    _ _ hab'
  have h' :=
    (ConcreteCategory.congr_hom ((stableSystemMap (inclusion E f i) d).naturality hm) a).trans
      (h.trans
        (ConcreteCategory.congr_hom ((stableSystemMap (inclusion E f j) d).naturality hn) b).symm)
  obtain ⟨N, hi, hj, hN⟩ := exists_eventual_stableStage_eq E f d l
    ((stableSystem (E i) d).map hm a) ((stableSystem (E j) d).map hn b) h'
  refine ⟨N, hi, hj, ?_⟩
  have hleft := congrArg ((stableHomotopyFunctor d).map (transition E f i N hi))
    (colimit.w_apply (stableSystem (E i) d) hm a)
  have hright := congrArg ((stableHomotopyFunctor d).map (transition E f j N hj))
    (colimit.w_apply (stableSystem (E j) d) hn b)
  change (stableHomotopyFunctor d).map (transition E f i N hi)
      (stableHomotopyι (E i) d l ((stableSystem (E i) d).map hm a)) = _ at hleft
  change (stableHomotopyFunctor d).map (transition E f j N hj)
      (stableHomotopyι (E j) d l ((stableSystem (E j) d).map hn b)) = _ at hright
  exact hleft.symm.trans
    ((ConcreteCategory.congr_hom (stableHomotopyι_naturality (transition E f i N hi) d l)
      ((stableSystem (E i) d).map hm a)).trans
        ((congrArg (stableHomotopyι (E N) d l) hN).trans
          ((ConcreteCategory.congr_hom (stableHomotopyι_naturality (transition E f j N hj) d l)
            ((stableSystem (E j) d).map hn b)).symm.trans hright)))

omit [∀ i k, T1Space ((E i).space k)] in
/-- The actual stable inclusion agrees with its original finite-transition factorization. -/
theorem inclusion_transition_stableMap {i N : ℕ} (hi : i ≤ N) (d : ℤ) :
    (stableHomotopyFunctor d).map (inclusion E f i) =
      (stableHomotopyFunctor d).map (transition E f i N hi) ≫
        (stableHomotopyFunctor d).map (inclusion E f N) := by
  rw [← Functor.map_comp]
  exact (inclusionTransitionHomotopy E f hi).stableHomotopyMap_eq d

end Topology.LoopPrespectrum.Telescope
