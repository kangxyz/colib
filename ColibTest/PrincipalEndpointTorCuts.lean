/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.EndpointTorCuts

/-!
# Actual endpoint stalk Tor regression tests

The tests retain arbitrary local rings, arbitrary truncation bounds, the zero
quotient, an unreduced squared principal equation, and the literal polynomial
numerator and denominator at both original endpoints. No component flatness or
graph coefficient comparison is supplied.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order
open AlgebraicGeometry.PrincipalFamilyUnitOpen
open AlgebraicGeometry.PrincipalFamilyEndpointCuts
open scoped BigOperators

universe u

section Algebra

variable {R S : Type u} [CommRing R] [CommRing S] [IsDomain S]

-- A squared equation remains the actual quotient; no radical is inserted.
example (φ : R →+* S) (c n : R) (hc : IsSMulRegular R c)
    (hker : RingHom.ker φ = Ideal.span {c}) (hn : φ n ≠ 0) :
    IsSMulRegular (R ⧸ Ideal.span {n ^ 2}) c := by
  apply Module.isSMulRegular_quotient_span_swap c (n ^ 2) hc
  rw [← hker]
  apply Module.isSMulRegular_quotient_ker_of_domain_image
  simpa only [map_pow] using pow_ne_zero 2 hn

-- The zero quotient is included, for every truncation that contains degree zero.
example [IsLocalRing R] (c : R) (hc : IsSMulRegular R c)
    (hcm : c ∈ IsLocalRing.maximalIdeal R) (b : ℕ) :
    (∑ i ∈ Finset.range (b + 1), (-1 : ℤ) ^ i *
      ((Module.length R (((Tor (ModuleCat R) i).obj
        (ModuleCat.of R (R ⧸ Ideal.span {c}))).obj
          (ModuleCat.of R (R ⧸ (⊤ : Ideal R))))).toNat : ℤ)) = 0 := by
  have htop : IsSMulRegular (R ⧸ (⊤ : Ideal R)) c :=
    fun _ _ _ => Subsingleton.elim _ _
  rw [Module.sum_tor_principal_length_of_regular c hc hcm ⊤ htop b]
  simp

-- Every higher degree vanishes from regularity, with no flatness assumption on M.
example [IsLocalRing R] (c : R) (hc : IsSMulRegular R c)
    (hcm : c ∈ IsLocalRing.maximalIdeal R)
    (M : Type u) [AddCommGroup M] [Module R M] (hM : IsSMulRegular M c) (n : ℕ) :
    IsZero (((Tor (ModuleCat R) (n + 1)).obj
      (ModuleCat.of R (R ⧸ Ideal.span {c}))).obj (ModuleCat.of R M)) :=
  Module.isZero_tor_principal_of_regular c hc hcm M hM (n + 1) (Nat.succ_ne_zero n)

end Algebra

section Geometry

variable {k : Type u} [Field k] {W : Scheme.{u}} (p : W ⟶ Spec (.of k))
    [IsIntegral W] [IsNoetherian W] [IsNoetherian (parameterSpace p)]
    (a b : Γ(W, ⊤)) (x : W) (hx : coheight x = 1)
    (ha : W.presheaf.germ ⊤ x (by trivial) a ≠ 0)
    (hb : W.presheaf.germ ⊤ x (by trivial) b ≠ 0)

-- The first Tor argument is the actual original endpoint stalk with its stalk-map action.
example (c : k) (s : Γ(parameterSpace p, ⊤))
    (hs : W.presheaf.germ ⊤ x (by trivial) ((endpoint p c).appTop s) ≠ 0) :
    weightedEndpointStalkTor p c x s = ((cutLength p c x s).toNat : ℤ) :=
  weightedEndpointStalkTor_eq_cutLength p c x hx s hs

-- At zero, the numerator's unspecialized a need not have a nonzero germ.
example : weightedEndpointStalkTor p 0 x (numerator p a b) -
    weightedEndpointStalkTor p 0 x (denominator p b) = 0 :=
  weightedEndpointStalkTor_difference_zero p a b x hx hb

-- At one, the same original fraction and the original numerator-minus-denominator sign remain.
example : weightedEndpointStalkTor p 1 x (numerator p a b) -
    weightedEndpointStalkTor p 1 x (denominator p b) =
    W.ord (algebraMap (W.presheaf.stalk x) W.functionField
        (W.presheaf.germ ⊤ x (by trivial) a) /
      algebraMap (W.presheaf.stalk x) W.functionField
        (W.presheaf.germ ⊤ x (by trivial) b)) x :=
  weightedEndpointStalkTor_difference_one p a b x hx ha hb

end Geometry

#print axioms Module.quotient_tor_associativity
#print axioms Module.principal_quotient_tor_associativity_of_surjective
#print axioms AlgebraicGeometry.PrincipalFamilyEndpointCuts.weightedEndpointStalkTor_eq_cutLength
#print axioms AlgebraicGeometry.PrincipalFamilyEndpointCuts.weightedEndpointStalkTor_difference_zero
#print axioms AlgebraicGeometry.PrincipalFamilyEndpointCuts.weightedEndpointStalkTor_difference_one
