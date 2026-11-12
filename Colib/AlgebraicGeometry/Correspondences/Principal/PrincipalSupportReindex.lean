/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.SignedLocalPrincipalCuts
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycle

/-!
# Exact local-prime indexing of original principal-cycle supports

The original nonzero principal-cycle supports specializing to a point are
precisely the actual local numerator/denominator minimal primes whose signed
order does not cancel. The map is the original scheme fromSpecStalk, and the
point on each integral support is determined by its original closed immersion.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (x : X)

/-- Original nonzero principal-cycle supports passing through the chosen point. -/
abbrev principalSupportThrough (F : X.functionField) : Set X :=
  {z | z ∈ (principalCycle X F).support ∧ z ⤳ x}

/-- The contributing local primes, after genuine signed cancellation. -/
abbrev nonzeroLocalPrincipalPrimes (n d : X.presheaf.stalk x) :=
  {q : PrimeSpectrum (X.presheaf.stalk x) |
    q ∈ localPrincipalPrimes X x n ∪ localPrincipalPrimes X x d ∧
      X.ord (algebraMap (X.presheaf.stalk x) X.functionField n /
        algebraMap (X.presheaf.stalk x) X.functionField d) (X.fromSpecStalk x q) ≠ 0}

/-- A nonzero original signed order forces membership in the actual local
numerator or denominator minimal support, not an assumed divisor decomposition. -/
theorem mem_localPrincipalPrimes_union_of_ord_ne_zero
    (n d : X.presheaf.stalk x) (hn : n ≠ 0) (hd : d ≠ 0)
    (q : PrimeSpectrum (X.presheaf.stalk x))
    (ho : X.ord (algebraMap (X.presheaf.stalk x) X.functionField n /
      algebraMap (X.presheaf.stalk x) X.functionField d) (X.fromSpecStalk x q) ≠ 0) :
    q ∈ localPrincipalPrimes X x n ∪ localPrincipalPrimes X x d := by
  have hheight : Order.coheight (X.fromSpecStalk x q) = 1 := by
    by_contra hne
    exact ho (Scheme.ord_eq_zero_of_coheight_neq_one hne _)
  by_contra hnot
  have hnq : ¬ Minimal (· ∈ Module.support (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ Ideal.span {n})) q := fun h => hnot (Or.inl h)
  have hdq : ¬ Minimal (· ∈ Module.support (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ Ideal.span {d})) q := fun h => hnot (Or.inr h)
  apply ho
  rw [X.ord_div_eq_localizedPrincipalWeights x q n d hn hd hheight,
    X.length_localizedPrincipalQuotient_eq_zero_of_not_minimal x n hn q hheight hnq,
    X.length_localizedPrincipalQuotient_eq_zero_of_not_minimal x d hd q hheight hdq]
  simp

/-- Actual local primes are in bijection with the original nonzero principal-cycle
supports through the point. All signed cancellations are retained. -/
theorem bijOn_fromSpecStalk_nonzeroPrincipalSupport
    (n d : X.presheaf.stalk x) (hn : n ≠ 0) (hd : d ≠ 0) :
    Set.BijOn (X.fromSpecStalk x) (nonzeroLocalPrincipalPrimes X x n d)
      (principalSupportThrough X x
        (algebraMap (X.presheaf.stalk x) X.functionField n /
          algebraMap (X.presheaf.stalk x) X.functionField d)) := by
  refine ⟨?_, (X.fromSpecStalk x).isEmbedding.injective.injOn, ?_⟩
  · intro q hq
    exact ⟨hq.2, X.fromSpecStalk_specializes x q⟩
  · intro z hz
    obtain ⟨q, hq⟩ := Stacks.Chow.exists_fromSpecStalk_eq hz.2
    refine ⟨q, ⟨?_, ?_⟩, hq⟩
    · apply mem_localPrincipalPrimes_union_of_ord_ne_zero X x n d hn hd q
      simpa only [hq, Function.locallyFinsuppWithin.support, Function.mem_support,
        principalCycle_apply] using hz.1
    · simpa only [hq, Function.locallyFinsuppWithin.support, Function.mem_support,
        principalCycle_apply] using hz.1

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The original integral support contains the original specialization point. -/
theorem exists_integralComponentPointOfSpecializes (z : X) (h : z ⤳ x) :
    ∃ e : (integralComponentAt z).subscheme, (integralComponentAt z).subschemeι e = x := by
  rw [← Set.mem_range, (integralComponentAt z).range_subschemeι, coe_support_integralComponentAt]
  exact h.mem_closure

/-- The actual point on an original integral support above a specialization. -/
def integralComponentPointOfSpecializes (z : X) (h : z ⤳ x) :
    (integralComponentAt z).subscheme :=
  (exists_integralComponentPointOfSpecializes X x z h).choose

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The chosen support point maps to the unchanged original ambient point. -/
@[simp] theorem integralComponentPointOfSpecializes_inclusion (z : X) (h : z ⤳ x) :
    (integralComponentAt z).subschemeι (integralComponentPointOfSpecializes X x z h) = x :=
  (exists_integralComponentPointOfSpecializes X x z h).choose_spec

/-- The native full cut on an original integral support through the point. -/
def principalSupportCutLength (z : X) (s : Γ(X, ⊤)) : ℤ :=
  if h : z ⤳ x then
    let D := (integralComponentAt z).subscheme
    let e := integralComponentPointOfSpecializes X x z h
    (Module.length (D.presheaf.stalk e)
      (D.presheaf.stalk e ⧸ Ideal.span {(D.presheaf.germ ⊤ e (by trivial)
        ((integralComponentAt z).subschemeι.appTop s))})).toNat
  else 0

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The actual local and global support points agree by closed-immersion
injectivity, so their full cut lengths agree without a module comparison premise. -/
theorem integralSupportCutLength_eq_principalSupportCutLength
    (q : PrimeSpectrum (X.presheaf.stalk x)) (s : Γ(X, ⊤)) :
    integralSupportCutLength X x s q =
      principalSupportCutLength X x (X.fromSpecStalk x q) s := by
  rw [principalSupportCutLength, dite_eq_left (X.fromSpecStalk_specializes x q)]
  have he : integralComponentPointOverStalk X x q =
      integralComponentPointOfSpecializes X x (X.fromSpecStalk x q)
        (X.fromSpecStalk_specializes x q) := by
    apply (integralComponentAt (X.fromSpecStalk x q)).subschemeι.isEmbedding.injective
    simp only [integralComponentPointOverStalk_inclusion,
      integralComponentPointOfSpecializes_inclusion]
  exact congrArg (fun e : (integralComponentAt (X.fromSpecStalk x q)).subscheme =>
    ((Module.length ((integralComponentAt (X.fromSpecStalk x q)).subscheme.presheaf.stalk e)
      ((integralComponentAt (X.fromSpecStalk x q)).subscheme.presheaf.stalk e ⧸
        Ideal.span {((integralComponentAt (X.fromSpecStalk x q)).subscheme.presheaf.germ
          ⊤ e (by trivial)
          ((integralComponentAt (X.fromSpecStalk x q)).subschemeι.appTop s))})).toNat : ℤ)) he

end Stacks.Chow
