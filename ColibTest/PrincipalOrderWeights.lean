/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.OrderWeights
import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyUnitOpen

/-!
# Original principal order localization tests

Squared equations stay unreduced. The original polynomial family's actual
ambient rational function receives a genuine fraction presentation without a
supplied comparison certificate. Neither polynomial numerator matching nor
finite-pushforward compatibility is asserted.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open AlgebraicGeometry.PrincipalFamilyUnitOpen

universe u

-- The full squared principal equation is localized without taking its radical.
example (X : Scheme.{u}) (x : X) (q : PrimeSpectrum (X.presheaf.stalk x))
    (n : X.presheaf.stalk x) :
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl (X.presheaf.stalk x ⧸ Ideal.span {n ^ 2})) =
    Module.length (X.presheaf.stalk (X.fromSpecStalk x q))
      (X.presheaf.stalk (X.fromSpecStalk x q) ⧸ Ideal.span
        {X.presheaf.stalkSpecializes (X.fromSpecStalk_specializes x q) (n ^ 2)}) :=
  X.length_localizedPrincipalQuotient_eq_stalkQuotient x q (n ^ 2)

-- Inverting the same fraction reverses the numerator-minus-denominator sign.
example (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (q : PrimeSpectrum (X.presheaf.stalk x))
    (n d : X.presheaf.stalk x) (hn : n ≠ 0) (hd : d ≠ 0)
    (hq : coheight (X.fromSpecStalk x q) = 1) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField d /
      algebraMap (X.presheaf.stalk x) X.functionField n) (X.fromSpecStalk x q) =
    ((Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl
        (X.presheaf.stalk x ⧸ Ideal.span {d}))).toNat : ℤ) -
    ((Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl
        (X.presheaf.stalk x ⧸ Ideal.span {n}))).toNat : ℤ) :=
  X.ord_div_eq_localizedPrincipalWeights x q d n hd hn hq

-- Specialize to the actual original polynomial family's native rational function.
example {R : Type u} [CommRing R] {C W : Scheme.{u}}
    (p : C ⟶ Spec (.of R)) (v : W ⟶ C) [IsOpenImmersion v]
    [IsIntegral (parameterSpace p)] [IsLocallyNoetherian (parameterSpace p)]
    (f : Γ(W, ⊤)) [Nonempty (ambientUnitOpen p v f)] (x : parameterSpace p) :
    ∃ n d : (parameterSpace p).presheaf.stalk x, n ≠ 0 ∧ d ≠ 0 ∧
      algebraMap ((parameterSpace p).presheaf.stalk x) (parameterSpace p).functionField n /
        algebraMap ((parameterSpace p).presheaf.stalk x) (parameterSpace p).functionField d =
          ambientRationalFunction p v f ∧
      ∀ q : PrimeSpectrum ((parameterSpace p).presheaf.stalk x),
        coheight ((parameterSpace p).fromSpecStalk x q) = 1 →
        (parameterSpace p).ord (ambientRationalFunction p v f)
          ((parameterSpace p).fromSpecStalk x q) =
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl
              ((parameterSpace p).presheaf.stalk x ⧸ Ideal.span {n}))).toNat : ℤ) -
          ((Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl
              ((parameterSpace p).presheaf.stalk x ⧸ Ideal.span {d}))).toNat : ℤ) := by
  apply (parameterSpace p).exists_localPrincipalWeights x (ambientRationalFunction p v f)
  exact ((isUnit_ambientUnitSection p v f).map
    ((parameterSpace p).germToFunctionField (ambientUnitOpen p v f)).hom).ne_zero

#print axioms AlgebraicGeometry.Scheme.length_localizedPrincipalQuotient_eq_stalkQuotient
#print axioms AlgebraicGeometry.Scheme.ord_div_eq_localizedPrincipalWeights
#print axioms AlgebraicGeometry.Scheme.exists_localPrincipalWeights
