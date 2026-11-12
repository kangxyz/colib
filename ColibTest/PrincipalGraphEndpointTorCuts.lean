/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.GraphEndpointTorCuts

/-! # Actual native graph-incidence parameter-cut regression tests -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.PrincipalFamilyUnitOpen Stacks.Chow

universe u

variable {k : Type u} [Field k] {X Z : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))

/-- The native incidence coefficient, without support flatness, is the full cut. -/
example
    [IsIntegral X] [IsSeparated p] [Smooth p] [Smooth h]
    (c : k) (s : genericPoints X)
    (w : pullback (C := Scheme) (projection p ≫ p) h)
    [IsDominant ((integralComponentAt w).subschemeι ≫
      pullback.fst (projection p ≫ p) h ≫
        pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))]
    (t : genericPoints (correspondenceIncidence p (projection p ≫ p) h
      (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val) w)) :
    correspondenceIncidenceTorCoefficient k p (projection p ≫ p) h
      (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val) w t =
      ((Module.length
        ((integralComponentAt w).subscheme.presheaf.stalk (pullback.snd (C := Scheme) _ _ t.val))
        ((integralComponentAt w).subscheme.presheaf.stalk (pullback.snd (C := Scheme) _ _ t.val) ⧸
          Ideal.span {((integralComponentAt w).subscheme.presheaf.germ ⊤
            (pullback.snd (C := Scheme) _ _ t.val) (by trivial)
            (PolynomialEndpointFiber.equation ((integralComponentAt w).subschemeι ≫
              pullback.fst (projection p ≫ p) h ≫
                pullback.snd p (Spec.map
                  (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) c))})).toNat : ℤ) :=
  graphIncidenceTorCoefficient_eq_parameterCut p h c s w t

/-- Regularity only concerns the structural ambient morphism. -/
example {P : Scheme.{u}} (f : P ⟶ Spec (.of (Polynomial k))) [Flat f]
    (c : k) (x : P) :
    IsSMulRegular (P.presheaf.stalk x)
      (P.presheaf.germ ⊤ x (by trivial) (PolynomialEndpointFiber.equation f c)) :=
  PolynomialEndpointFiber.equation_germ_isSMulRegular_of_flat f c x

section

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- Full extended lengths agree before coefficient extraction. -/
example
    (φ : R →+* S) (hφ : Function.Surjective φ)
    (ψ : R →+* T) (hψ : Function.Surjective ψ)
    (c : R) (hker : RingHom.ker φ = Ideal.span {c}) :
    Module.length R (((Tor (ModuleCat R) 0).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))).obj
        ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of T T))) =
      Module.length T (T ⧸ Ideal.span {ψ c}) :=
  Module.length_torZero_surjective_principal_cut φ hφ ψ hψ c hker

end

#print axioms Module.length_torZero_surjective_principal_cut
#print axioms Module.length_tor_two_surjective_targets
#print axioms Module.sum_tor_surjective_principal_cut
#print axioms Stacks.Chow.PolynomialEndpointFiber.equation_germ_isSMulRegular_of_flat
#print axioms AlgebraicGeometry.Scheme.Hom.transported_stalkMap_surjective
#print axioms AlgebraicGeometry.Scheme.Hom.transported_stalkMap_ker
#print axioms AlgebraicGeometry.Scheme.Hom.transported_stalkMap_globalSection
#print axioms Stacks.Chow.graphEndpoint_stalkTor_eq_parameterCut
#print axioms Stacks.Chow.graphIncidenceTorCoefficient_eq_parameterCut
