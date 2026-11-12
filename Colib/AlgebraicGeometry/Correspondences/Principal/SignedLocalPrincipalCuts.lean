/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.IntegralComponentStalkCuts
public import Colib.AlgebraicGeometry.Correspondences.Principal.LocalPrincipalWeightSupport

/-!
# Signed original orders and full endpoint cuts

Native local Euler associativity for numerator and denominator is combined on
their actual finite union of minimal support primes. The coefficient there is
the original Scheme.ord of their unchanged fraction, and the cut is the full
quotient on the original integral support. Noncontributing weights vanish
before conversion from extended lengths to integer coefficients.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (x : X)

/-- Actual minimal support primes of the full local principal quotient. -/
abbrev localPrincipalPrimes (n : X.presheaf.stalk x) :=
  {q : PrimeSpectrum (X.presheaf.stalk x) |
    Minimal (· ∈ Module.support (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ Ideal.span {n})) q}

/-- Actual localized full principal length, with the native integer convention. -/
abbrev localPrincipalWeight (n : X.presheaf.stalk x)
    (q : PrimeSpectrum (X.presheaf.stalk x)) : ℤ :=
  (Module.length (Localization.AtPrime q.asIdeal)
    (LocalizedModule q.asIdeal.primeCompl (X.presheaf.stalk x ⧸ Ideal.span {n}))).toNat

/-- The full original support cut at the actual point over the ambient stalk. -/
abbrev integralSupportCutLength (s : Γ(X, ⊤)) (q : PrimeSpectrum (X.presheaf.stalk x)) : ℤ :=
  let D := (integralComponentAt (X.fromSpecStalk x q)).subscheme
  let e := integralComponentPointOverStalk X x q
  (Module.length (D.presheaf.stalk e)
    (D.presheaf.stalk e ⧸ Ideal.span {(D.presheaf.germ ⊤ e (by trivial)
      ((integralComponentAt (X.fromSpecStalk x q)).subschemeι.appTop s))})).toNat

/-- An original fraction's signed orders weight the actual full support cuts to
give the full numerator-minus-denominator endpoint quotient length. -/
@[colib_tag "COL-1077", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/FlatPullbackPrincipalDiviso\
    r.lean:585-627"
  "ingredient" "Original local fraction and order as full quotient-length difference; the \
    support and endpoint assembly is proved here."]
theorem signed_ord_integralSupportCuts_eq_endpointDifference
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
    let hN := AlgebraicGeometry.finite_minimal_support
      (R := X.presheaf.stalk x) (M := X.presheaf.stalk x ⧸ Ideal.span {n})
    let hD := AlgebraicGeometry.finite_minimal_support
      (R := X.presheaf.stalk x) (M := X.presheaf.stalk x ⧸ Ideal.span {d})
    ∑ q ∈ hN.toFinset ∪ hD.toFinset,
      X.ord (algebraMap (X.presheaf.stalk x) X.functionField n /
        algebraMap (X.presheaf.stalk x) X.functionField d) (X.fromSpecStalk x q) *
          integralSupportCutLength X x s q =
      ((Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ (Ideal.span {X.presheaf.germ ⊤ x (by trivial) s} ⊔
          Ideal.span {n}))).toNat : ℤ) -
      ((Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ (Ideal.span {X.presheaf.germ ⊤ x (by trivial) s} ⊔
          Ideal.span {d}))).toNat : ℤ) := by
  classical
  let hN := AlgebraicGeometry.finite_minimal_support
    (R := X.presheaf.stalk x) (M := X.presheaf.stalk x ⧸ Ideal.span {n})
  let hD := AlgebraicGeometry.finite_minimal_support
    (R := X.presheaf.stalk x) (M := X.presheaf.stalk x ⧸ Ideal.span {d})
  let T := hN.toFinset ∪ hD.toFinset
  have hT (q) (hq : q ∈ T) : q ∈ localPrincipalPrimes X x n ∨
      q ∈ localPrincipalPrimes X x d := by
    simpa only [T, Finset.mem_union, Set.Finite.mem_toFinset] using hq
  have hheight (q) (hq : q ∈ T) : Order.coheight (X.fromSpecStalk x q) = 1 := by
    rcases hT q hq with hq | hq
    · exact X.coheight_fromSpecStalk_eq_one_of_minimal_principal_support x n hn q hq
    · exact X.coheight_fromSpecStalk_eq_one_of_minimal_principal_support x d hd q hq
  have extend (a : X.presheaf.stalk x) (ha : a ≠ 0)
      (hA : (localPrincipalPrimes X x a).Finite) (hsub : hA.toFinset ⊆ T) :
      (∑ q ∈ T, localPrincipalWeight X x a q * integralSupportCutLength X x s q) =
        ∑ᶠ q ∈ localPrincipalPrimes X x a,
          localPrincipalWeight X x a q * integralSupportCutLength X x s q := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hA]
    symm
    apply Finset.sum_subset hsub
    intro q hq hqa
    have hz := X.length_localizedPrincipalQuotient_eq_zero_of_not_minimal x a ha q
      (hheight q hq) (by
        simpa only [Set.Finite.mem_toFinset, localPrincipalPrimes, Set.mem_ofPred_eq] using hqa)
    simp only [localPrincipalWeight, hz, ENat.toNat_zero, Nat.cast_zero, zero_mul]
  calc
    _ = ∑ q ∈ T, (localPrincipalWeight X x n q - localPrincipalWeight X x d q) *
        integralSupportCutLength X x s q := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [X.ord_div_eq_localizedPrincipalWeights_of_minimal_support x n d hn hd q (hT q hq)]
    _ = (∑ q ∈ T, localPrincipalWeight X x n q * integralSupportCutLength X x s q) -
        ∑ q ∈ T, localPrincipalWeight X x d q * integralSupportCutLength X x s q := by
      simp only [sub_mul, Finset.sum_sub_distrib]
    _ = _ := by
      rw [extend n hn hN Finset.subset_union_left, extend d hd hD Finset.subset_union_right]
      exact congrArg₂ (· - ·)
        (principalCut_associativity_integralComponentStalks X x n s hsm hsn hfn).symm
        (principalCut_associativity_integralComponentStalks X x d s hsm hsd hfd).symm

end Stacks.Chow
