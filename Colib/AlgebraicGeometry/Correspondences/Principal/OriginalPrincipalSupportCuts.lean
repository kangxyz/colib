/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.PrincipalSupportReindex

/-!
# Full cuts indexed by the original principal cycle

The actual fromSpecStalk bijection reindexes the finite local-prime sum as a
sum over the original nonzero principalCycle supports through the ambient point.
Original signed coefficients and full support quotient lengths are retained.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (x : X)

/-- The original principal supports through this point form exactly the signed
local-prime sum, including cancellation of common numerator/denominator components. -/
theorem principalCycle_supportCuts_eq_localPrimeSum
    (n d : X.presheaf.stalk x) (hn : n ≠ 0) (hd : d ≠ 0) (s : Γ(X, ⊤)) :
    let F := algebraMap (X.presheaf.stalk x) X.functionField n /
      algebraMap (X.presheaf.stalk x) X.functionField d
    let hN := AlgebraicGeometry.finite_minimal_support
      (R := X.presheaf.stalk x) (M := X.presheaf.stalk x ⧸ Ideal.span {n})
    let hD := AlgebraicGeometry.finite_minimal_support
      (R := X.presheaf.stalk x) (M := X.presheaf.stalk x ⧸ Ideal.span {d})
    (∑ᶠ z ∈ principalSupportThrough X x F,
      (principalCycle X F) z * principalSupportCutLength X x z s) =
      ∑ q ∈ hN.toFinset ∪ hD.toFinset,
        X.ord F (X.fromSpecStalk x q) * integralSupportCutLength X x s q := by
  classical
  dsimp only
  let F := algebraMap (X.presheaf.stalk x) X.functionField n /
    algebraMap (X.presheaf.stalk x) X.functionField d
  let hN := AlgebraicGeometry.finite_minimal_support
    (R := X.presheaf.stalk x) (M := X.presheaf.stalk x ⧸ Ideal.span {n})
  let hD := AlgebraicGeometry.finite_minimal_support
    (R := X.presheaf.stalk x) (M := X.presheaf.stalk x ⧸ Ideal.span {d})
  have hT : (localPrincipalPrimes X x n ∪ localPrincipalPrimes X x d).Finite := hN.union hD
  have hQ : (nonzeroLocalPrincipalPrimes X x n d).Finite := hT.subset fun _ hq => hq.1
  have H := finsum_mem_eq_of_bijOn (X.fromSpecStalk x)
    (bijOn_fromSpecStalk_nonzeroPrincipalSupport X x n d hn hd)
    (f := fun q => X.ord F (X.fromSpecStalk x q) * integralSupportCutLength X x s q)
    (g := fun z => (principalCycle X F) z * principalSupportCutLength X x z s)
    (fun q _ => congrArg (fun a => X.ord F (X.fromSpecStalk x q) * a)
      (integralSupportCutLength_eq_principalSupportCutLength X x q s))
  rw [← H]
  change (∑ᶠ q ∈ nonzeroLocalPrincipalPrimes X x n d,
    X.ord F (X.fromSpecStalk x q) * integralSupportCutLength X x s q) = _
  rw [finsum_mem_eq_finite_toFinset_sum _ hQ]
  apply Finset.sum_subset
  · intro q hq
    have h := (hQ.mem_toFinset.mp hq).1
    simpa only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_union,
      localPrincipalPrimes] using h
  · intro q _ hq
    have hzero : X.ord F (X.fromSpecStalk x q) = 0 := by
      by_contra hnzero
      apply hq
      apply hQ.mem_toFinset.mpr
      exact ⟨mem_localPrincipalPrimes_union_of_ord_ne_zero X x n d hn hd q hnzero, hnzero⟩
    rw [hzero, zero_mul]

/-- The original principal-cycle coefficient sum, with its genuine supports,
equals the full endpoint numerator-minus-denominator quotient length. -/
@[colib_tag "COL-1080"]
theorem principalCycle_supportCuts_eq_endpointDifference
    (n d : X.presheaf.stalk x) (hn : n ≠ 0) (hd : d ≠ 0) (s : Γ(X, ⊤))
    (hsm : X.presheaf.germ ⊤ x (by trivial) s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hsn : IsSMulRegular (X.presheaf.stalk x ⧸ Ideal.span {n})
      (X.presheaf.germ ⊤ x (by trivial) s))
    (hsd : IsSMulRegular (X.presheaf.stalk x ⧸ Ideal.span {d})
      (X.presheaf.germ ⊤ x (by trivial) s))
    (hfn : Module.length (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ (Ideal.span {X.presheaf.germ ⊤ x (by trivial) s} ⊔
        Ideal.span {n})) ≠ ⊤)
    (hfd : Module.length (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ (Ideal.span {X.presheaf.germ ⊤ x (by trivial) s} ⊔
        Ideal.span {d})) ≠ ⊤) :
    let F := algebraMap (X.presheaf.stalk x) X.functionField n /
      algebraMap (X.presheaf.stalk x) X.functionField d
    (∑ᶠ z ∈ principalSupportThrough X x F,
      (principalCycle X F) z * principalSupportCutLength X x z s) =
      ((Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ (Ideal.span {X.presheaf.germ ⊤ x (by trivial) s} ⊔
          Ideal.span {n}))).toNat : ℤ) -
      ((Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ (Ideal.span {X.presheaf.germ ⊤ x (by trivial) s} ⊔
          Ideal.span {d}))).toNat : ℤ) := by
  dsimp only
  rw [principalCycle_supportCuts_eq_localPrimeSum X x n d hn hd s]
  exact signed_ord_integralSupportCuts_eq_endpointDifference X x n d hn hd s hsm hsn hsd hfn hfd

end Stacks.Chow
