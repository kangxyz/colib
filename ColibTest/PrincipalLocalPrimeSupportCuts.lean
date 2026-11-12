/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.SignedLocalPrincipalCuts

/-! # Actual local prime support cuts and original order weights -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

attribute [local instance] Classical.propDecidable

universe u

section
variable (X : Scheme.{u}) (x : X)

/-- The full actual support-cut associativity needs no integral ambient premise. -/
example [IsLocallyNoetherian X]
    (n : X.presheaf.stalk x) (s : Γ(X, ⊤))
    (hsm : X.presheaf.germ ⊤ x (by trivial) s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hs : IsSMulRegular (X.presheaf.stalk x ⧸ Ideal.span {n})
      (X.presheaf.germ ⊤ x (by trivial) s))
    (hfinite : Module.length (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ (Ideal.span {X.presheaf.germ ⊤ x (by trivial) s} ⊔
        Ideal.span {n})) ≠ ⊤) :
    ((Module.length (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ (Ideal.span {X.presheaf.germ ⊤ x (by trivial) s} ⊔
        Ideal.span {n}))).toNat : ℤ) =
    ∑ᶠ q ∈ {q : PrimeSpectrum (X.presheaf.stalk x) |
        Minimal (· ∈ Module.support (X.presheaf.stalk x)
          (X.presheaf.stalk x ⧸ Ideal.span {n})) q},
      ((Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl (X.presheaf.stalk x ⧸ Ideal.span {n}))).toNat : ℤ) *
      let D := (integralComponentAt (X.fromSpecStalk x q)).subscheme
      let e := integralComponentPointOverStalk X x q
      ((Module.length (D.presheaf.stalk e)
        (D.presheaf.stalk e ⧸ Ideal.span {(D.presheaf.germ ⊤ e (by trivial)
          ((integralComponentAt (X.fromSpecStalk x q)).subschemeι.appTop s))})).toNat : ℤ) :=
  principalCut_associativity_integralComponentStalks X x n s hsm hs hfinite

end

section
variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (x : X)

/-- Contributing numerator/denominator primes supply their own codimension. -/
example
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
          (X.presheaf.stalk x ⧸ Ideal.span {d}))).toNat : ℤ) :=
  X.ord_div_eq_localizedPrincipalWeights_of_minimal_support x n d hn hd q hq

end

#print axioms Stacks.Chow.exists_integralComponentAt_point_over_stalk
#print axioms Stacks.Chow.integralComponentAt_transported_stalkMap_ker
#print axioms Stacks.Chow.integralComponentAt_primeCut_length
#print axioms Stacks.Chow.principalCut_associativity_integralComponentStalks
#print axioms AlgebraicGeometry.Scheme.coheight_fromSpecStalk_eq_one_of_minimal_principal_support
#print axioms AlgebraicGeometry.Scheme.ord_div_eq_localizedPrincipalWeights_of_minimal_support

section
variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (x : X)

/-- Original signed orders weight full support cuts, with no reduced quotient substitution. -/
example
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
          Ideal.span {d}))).toNat : ℤ) :=
  signed_ord_integralSupportCuts_eq_endpointDifference X x n d hn hd s hsm hsn hsd hfn hfd

end

#print axioms AlgebraicGeometry.Scheme.length_localizedPrincipalQuotient_eq_zero_of_not_minimal
#print axioms Stacks.Chow.signed_ord_integralSupportCuts_eq_endpointDifference
