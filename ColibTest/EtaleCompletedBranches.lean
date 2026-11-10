/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.AdicCompletion.EtaleBranches

open IsLocalRing AdicCompletion

noncomputable section

universe u v

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [Algebra.Etale R S]
  [DecidableEq (Ideal S)]

example (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    Module.Finite (AdicCompletion (maximalIdeal R) R)
        (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q) ∧
      Algebra.Etale (AdicCompletion (maximalIdeal R) R)
        (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q) :=
  localCompletionBaseFiniteEtale R S q

example (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    Stacks.DiscreteValuationRing.Ramification.ramificationIdx
      (AdicCompletion (maximalIdeal R) R)
      (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q) = 1 :=
  localCompletion_ramificationIdx_eq_one_of_etale R S q

example (q : IdealBranch ((maximalIdeal R).map (algebraMap R S))) :
    letI := localCompletionBaseAlgebra (maximalIdeal R) q
    letI := localCompletionBase_isLocalHom R S q
    Algebra.IsSeparable (ResidueField (AdicCompletion (maximalIdeal R) R))
      (ResidueField (BranchCompletion ((maximalIdeal R).map (algebraMap R S)) q)) :=
  localCompletion_residue_isSeparable_of_etale R S q
