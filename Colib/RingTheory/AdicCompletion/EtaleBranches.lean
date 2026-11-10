/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdicCompletion.BranchLocal
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Unramified.LocalRing
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex

/-!
# Finite étale actual completed branches

For a finite étale Dedekind algebra over a DVR, every original branch completion
is finite étale over the completed base. The algebra structure is exactly the
existing `localCompletionBaseAlgebra`; its ramification index is one and its
actual residue extension is separable in arbitrary characteristic.

The proof transports étaleness through the existing full tensor decomposition,
then uses the finite-product criterion. It assumes neither separability of an
earlier auxiliary extension nor invertibility of any degree. This is branch
geometry, not the all-symbol Milnor norm-residue square.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u v

namespace AdicCompletion

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [Algebra.Etale R S]
  [DecidableEq (Ideal S)]

/-- Every actual normalized-ideal branch stays finite étale after completing
both its original localization and the base, with the established base map. -/
theorem localCompletionBaseFiniteEtale
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    Module.Finite (AdicCompletion (maximalIdeal R) R)
        (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q) ∧
      Algebra.Etale (AdicCompletion (maximalIdeal R) R)
        (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q) := by
  let := fun j ↦ localCompletionBaseAlgebra (S := S) (maximalIdeal R) j
  let T := AdicCompletion (maximalIdeal R) R
  let U := fun j : IdealBranch ((maximalIdeal R).map (algebraMap R S)) ↦
    BranchCompletion ((maximalIdeal R).map (algebraMap R S)) j
  have hne := map_maximalIdeal_ne_zero R S
  let : Algebra.FormallyEtale T (∀ j, U j) :=
    Algebra.FormallyEtale.of_equiv (tensorEquivLocalCompletionsBase (maximalIdeal R) hne)
  let : Algebra.FormallyEtale T (U q) := (Algebra.FormallyEtale.pi_iff U).mp
    (show Algebra.FormallyEtale T (∀ j, U j) from inferInstance) q
  let : Module.Finite T (U q) := localCompletionBaseFinite (maximalIdeal R) hne q
  let : Algebra.FinitePresentation T (U q) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩

/-- The actual completed branch has ramification index one. This follows from
finite étaleness, not from separability of the generic extension alone. -/
theorem localCompletion_ramificationIdx_eq_one_of_etale
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    Stacks.DiscreteValuationRing.Ramification.ramificationIdx
      (AdicCompletion (maximalIdeal R) R)
      (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q) = 1 := by
  let := localCompletionBaseAlgebra (maximalIdeal R) q
  let T := AdicCompletion (maximalIdeal R) R
  let U := BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q
  let := (localCompletionBaseFiniteEtale R S q).2
  let := localCompletionBase_isLocalHom R S q
  have hmap : (maximalIdeal T).map (algebraMap T U) = maximalIdeal U :=
    Algebra.FormallyUnramified.map_maximalIdeal
  rw [Stacks.DiscreteValuationRing.Ramification.ramificationIdx_def, ← hmap]
  apply Ideal.ramificationIdx'_map_self_eq_one
  · rw [hmap]
    exact Ideal.IsMaximal.ne_top inferInstance
  · rw [hmap]
    exact IsDiscreteValuationRing.not_a_field U

/-- The actual residue extension of each completed branch is separable. -/
theorem localCompletion_residue_isSeparable_of_etale
    (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    letI := localCompletionBase_isLocalHom R S q
    Algebra.IsSeparable (ResidueField (AdicCompletion (maximalIdeal R) R))
      (ResidueField (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)) := by
  let := localCompletionBaseAlgebra (maximalIdeal R) q
  let := localCompletionBase_isLocalHom R S q
  let := (localCompletionBaseFiniteEtale R S q).2
  infer_instance

end AdicCompletion
