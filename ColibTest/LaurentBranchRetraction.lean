/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.LaurentBranchRetraction

open IsLocalRing Stacks.Chow

noncomputable section

universe u

example
    (k K : Type u) [Field k] [Field K]
    [Algebra (LaurentSeries k) K] [Algebra (PowerSeries k) K]
    [IsScalarTower (PowerSeries k) (LaurentSeries k) K]
    [FiniteDimensional (LaurentSeries k) K]
    [DecidableEq (Ideal (integralClosure (PowerSeries k) K))]
    (n : ℕ) (x : MilnorKTheory (ResidueField (PowerSeries k)) n)
    (hbranch :
      letI := PowerSeries.isDedekindDomain_integralClosure_laurentSeries k K
      letI := fun q => AdicCompletion.branchCompletionBase_isLocalHom
        (PowerSeries k) (integralClosure (PowerSeries k) K) q
      ∀ q : AdicCompletion.IdealBranch ((maximalIdeal (PowerSeries k)).map
          (algebraMap (PowerSeries k) (integralClosure (PowerSeries k) K))),
        (Stacks.DiscreteValuationRing.Ramification.ramificationIdx (PowerSeries k)
          (AdicCompletion.BranchCompletion ((maximalIdeal (PowerSeries k)).map
            (algebraMap (PowerSeries k) (integralClosure (PowerSeries k) K))) q) : ℤ) •
          milnorKTheoryMap (algebraMap (ResidueField (PowerSeries k))
            (ResidueField (AdicCompletion.BranchCompletion
              ((maximalIdeal (PowerSeries k)).map
                (algebraMap (PowerSeries k) (integralClosure (PowerSeries k) K))) q))) n x = 0) :
    (Module.finrank (LaurentSeries k) K : ℤ) • x = 0 :=
  finrank_smul_eq_zero_of_laurent_integralClosure_branches k K n x hbranch
