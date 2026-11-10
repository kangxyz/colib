/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.PowerSeries.FiniteNormalization
public import Colib.RingTheory.KTheory.MilnorK.Norm.BranchNormRetraction

/-!
# Retraction through every actual Laurent auxiliary branch

The Japanese property of the power-series base supplies finite Dedekind
normalization for every finite Laurent auxiliary extension. The existing full
branch degree-sum and residue norm retraction therefore apply without auxiliary
separability. Every actual normalization branch is retained with its original
ramification weight. No weight is cancelled and no norm-residue square is assumed.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace Stacks.Chow

/-- Branchwise ramification-weighted vanishing retracts to annihilation by the
actual finite Laurent auxiliary degree, including inseparable auxiliaries. -/
theorem finrank_smul_eq_zero_of_laurent_integralClosure_branches
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
    (Module.finrank (LaurentSeries k) K : ℤ) • x = 0 := by
  let := PowerSeries.isDedekindDomain_integralClosure_laurentSeries k K
  let := PowerSeries.finite_integralClosure_laurentSeries k K
  let : Module.IsTorsionFree (PowerSeries k) K :=
    Module.IsTorsionFree.trans_faithfulSMul (PowerSeries k) (LaurentSeries k) K
  let : Module.IsTorsionFree (PowerSeries k) (integralClosure (PowerSeries k) K) :=
    IsIntegralClosure.isTorsionFree (PowerSeries k) K
  let : IsFractionRing (integralClosure (PowerSeries k) K) K :=
    IsIntegralClosure.isFractionRing_of_finite_extension (PowerSeries k) (LaurentSeries k) K
      (integralClosure (PowerSeries k) K)
  exact finrank_smul_eq_zero_of_branchCompletion_ramification_smul_restrict_eq_zero
    (PowerSeries k) (integralClosure (PowerSeries k) K) (LaurentSeries k) K n x hbranch

end Stacks.Chow
