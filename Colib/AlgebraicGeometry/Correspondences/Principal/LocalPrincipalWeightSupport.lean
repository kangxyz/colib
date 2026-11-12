/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.OrderWeights
public import Colib.RingTheory.Multiplicity.PrincipalEuler.Associativity
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureHeightOneCorrespondence

/-!
# Original order weights on contributing local principal primes

A minimal support prime of a nonzero principal quotient has height one by the
native principal ideal theorem. Its original scheme point has coheight one,
so the original rational function's order is the difference of its actual
localized numerator and denominator lengths, without a coheight certificate.
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (x : X)

/-- Every contributing local principal prime gives a coheight-one original point. -/
theorem coheight_fromSpecStalk_eq_one_of_minimal_principal_support
    (n : X.presheaf.stalk x) (hn : n ≠ 0) (q : PrimeSpectrum (X.presheaf.stalk x))
    (hq : Minimal (· ∈ Module.support (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ Ideal.span {n})) q) :
    Order.coheight (X.fromSpecStalk x q) = 1 := by
  refine (Stacks.Chow.coheight_fromSpecStalk_eq_height x q).trans ?_
  have hmin := (AlgebraicGeometry.minimal_support_iff q).mp hq
  rw [Ideal.annihilator_quotient] at hmin
  exact le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {n}) q.asIdeal hmin)
    ((Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hn)).trans (Ideal.height_mono hmin.le))

/-- The original fraction's signed order is its true local-prime weight on every
prime contributing to either original principal quotient. -/
theorem ord_div_eq_localizedPrincipalWeights_of_minimal_support
    (n d : X.presheaf.stalk x) (hn : n ≠ 0) (hd : d ≠ 0)
    (q : PrimeSpectrum (X.presheaf.stalk x))
    (hq : Minimal (· ∈ Module.support (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ Ideal.span {n})) q ∨
      Minimal (· ∈ Module.support (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ Ideal.span {d})) q) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField n /
      algebraMap (X.presheaf.stalk x) X.functionField d) (X.fromSpecStalk x q) =
      ((Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl
          (X.presheaf.stalk x ⧸ Ideal.span {n}))).toNat : ℤ) -
      ((Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl
          (X.presheaf.stalk x ⧸ Ideal.span {d}))).toNat : ℤ) := by
  apply ord_div_eq_localizedPrincipalWeights X x q n d hn hd
  rcases hq with hq | hq
  · exact coheight_fromSpecStalk_eq_one_of_minimal_principal_support X x n hn q hq
  · exact coheight_fromSpecStalk_eq_one_of_minimal_principal_support X x d hd q hq

/-- At a coheight-one original point, a noncontributing principal weight is zero.
This is a full extended-length statement, not just vanishing after `toNat`. -/
theorem length_localizedPrincipalQuotient_eq_zero_of_not_minimal
    (n : X.presheaf.stalk x) (hn : n ≠ 0) (q : PrimeSpectrum (X.presheaf.stalk x))
    (hq : Order.coheight (X.fromSpecStalk x q) = 1)
    (hmin : ¬ Minimal (· ∈ Module.support (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ Ideal.span {n})) q) :
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl (X.presheaf.stalk x ⧸ Ideal.span {n})) = 0 := by
  have hheight : q.asIdeal.height = 1 :=
    (Stacks.Chow.coheight_fromSpecStalk_eq_height x q).symm.trans hq
  have hnot : q ∉ Module.support (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ Ideal.span {n}) := by
    intro hmem
    apply hmin
    apply (AlgebraicGeometry.minimal_support_iff q).mpr
    rw [Ideal.annihilator_quotient]
    have hle := Module.mem_support_iff_of_finite.mp hmem
    rw [Ideal.annihilator_quotient] at hle
    apply Ideal.mem_minimalPrimes_of_height_le hle
    rw [hheight]
    exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hn)
  have := Module.notMem_support_iff.mp hnot
  exact Module.length_eq_zero

end AlgebraicGeometry.Scheme
