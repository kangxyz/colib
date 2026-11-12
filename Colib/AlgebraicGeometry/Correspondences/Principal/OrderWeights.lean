/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.RingTheory.Length.LocalizationModelIndependence

/-!
# Original orders as actual local principal weights

At a prime of an actual scheme stalk, the corresponding generalization stalk
is its native localization. Localizing the full principal quotient therefore
computes its actual colength there. The original order of the same fraction is
the numerator weight minus the denominator weight, with no change of rational
function and no reduction of the principal quotients.

This identifies individual local weights. It does not identify either finite
pushforward or replace the required global sum over image collisions.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Order

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (x : X) (q : PrimeSpectrum (X.presheaf.stalk x))

/-- The actual point of a local prime specializes to the original stalk point. -/
theorem fromSpecStalk_specializes : X.fromSpecStalk x q ⤳ x :=
  X.range_fromSpecStalk.subset ⟨q, rfl⟩

/-- The full localized principal quotient has its literal colength in the
actual generalization stalk. This includes nilpotents and infinite lengths. -/
theorem length_localizedPrincipalQuotient_eq_stalkQuotient (n : X.presheaf.stalk x) :
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl (X.presheaf.stalk x ⧸ Ideal.span {n})) =
    Module.length (X.presheaf.stalk (X.fromSpecStalk x q))
      (X.presheaf.stalk (X.fromSpecStalk x q) ⧸ Ideal.span
        {X.presheaf.stalkSpecializes (fromSpecStalk_specializes X x q) n}) := by
  let R := X.presheaf.stalk x
  let S := X.presheaf.stalk (X.fromSpecStalk x q)
  let h := fromSpecStalk_specializes X x q
  let φ := (X.presheaf.stalkSpecializes h).hom
  let := φ.toAlgebra
  have : IsLocalization.AtPrime S q.asIdeal :=
    Stacks.Chow.isLocalization_stalk_of_specializes h q rfl
  have hsub : Submodule.localized' S q.asIdeal.primeCompl (Algebra.linearMap R S)
      (Ideal.span {n}) = Ideal.span {φ n} := by
    rw [Submodule.localized'_span]
    simp only [Set.image_singleton, Algebra.linearMap_apply]
    rfl
  have H := Module.length_eq_of_isLocalization_of_isLocalizedModule
    q.asIdeal.primeCompl S
    (Submodule.toLocalizedQuotient' S q.asIdeal.primeCompl (Algebra.linearMap R S)
      (Ideal.span {n}))
  rw [hsub] at H
  exact H

/-- The original order of the literal fraction is its numerator-minus-denominator
local principal weight. The function field element and its sign are unchanged. -/
theorem ord_div_eq_localizedPrincipalWeights [IsIntegral X] [IsLocallyNoetherian X]
    (n d : X.presheaf.stalk x) (hn : n ≠ 0) (hd : d ≠ 0)
    (hq : coheight (X.fromSpecStalk x q) = 1) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField n /
      algebraMap (X.presheaf.stalk x) X.functionField d) (X.fromSpecStalk x q) =
    ((Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl
        (X.presheaf.stalk x ⧸ Ideal.span {n}))).toNat : ℤ) -
    ((Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl
        (X.presheaf.stalk x ⧸ Ideal.span {d}))).toNat : ℤ) := by
  let h := fromSpecStalk_specializes X x q
  let φ := (X.presheaf.stalkSpecializes h).hom
  have hmap (a : X.presheaf.stalk x) :
      algebraMap (X.presheaf.stalk (X.fromSpecStalk x q)) X.functionField (φ a) =
        algebraMap (X.presheaf.stalk x) X.functionField a := by
    simp only [RingHom.algebraMap_toAlgebra]
    exact X.presheaf.stalkSpecializes_comp_apply _ h a
  have hφ : Function.Injective φ := by
    intro a b hab
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [← hmap a, ← hmap b, hab]
  rw [← hmap n, ← hmap d,
    Stacks.Chow.ord_div_algebraMap_eq_length_sub hq
      (fun hzero => hn (hφ (hzero.trans (map_zero φ).symm)))
      (fun hzero => hd (hφ (hzero.trans (map_zero φ).symm))),
    ← length_localizedPrincipalQuotient_eq_stalkQuotient X x q n,
    ← length_localizedPrincipalQuotient_eq_stalkQuotient X x q d]

/-- Every nonzero original rational function has a genuine local fraction whose
weights compute all codimension-one orders visible in this stalk. The fraction
presentation is produced from the native fraction-ring structure, not assumed. -/
@[colib_tag "COL-1053", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/FlatPullbackPrincipalDiviso\
    r.lean:585-627"
  "ingredient" "Original local fraction and order as full quotient-length difference; the \
    support and endpoint assembly is proved here."]
theorem exists_localPrincipalWeights [IsIntegral X] [IsLocallyNoetherian X]
    (F : X.functionField) (hF : F ≠ 0) :
    ∃ n d : X.presheaf.stalk x, n ≠ 0 ∧ d ≠ 0 ∧
      algebraMap (X.presheaf.stalk x) X.functionField n /
        algebraMap (X.presheaf.stalk x) X.functionField d = F ∧
      ∀ q : PrimeSpectrum (X.presheaf.stalk x), coheight (X.fromSpecStalk x q) = 1 →
        X.ord F (X.fromSpecStalk x q) =
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl
              (X.presheaf.stalk x ⧸ Ideal.span {n}))).toNat : ℤ) -
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl
              (X.presheaf.stalk x ⧸ Ideal.span {d}))).toNat : ℤ) := by
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (X.presheaf.stalk x) F
  have hn : n ≠ 0 := by
    intro hn
    apply hF
    rw [← hnd, hn, map_zero, zero_div]
  have hd' : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  refine ⟨n, d, hn, hd', hnd, ?_⟩
  intro q hq
  rw [← hnd]
  exact ord_div_eq_localizedPrincipalWeights X x q n d hn hd' hq

end AlgebraicGeometry.Scheme
