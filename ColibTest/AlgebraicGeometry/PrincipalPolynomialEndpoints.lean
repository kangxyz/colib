/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialCylinder
import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.EndpointOrder

/-!
# Tests of native principal polynomial endpoint maps and full local lengths

These checks retain arbitrary smooth sources, possibly nonreduced quotient cuts,
and the native order with its codimension and nonvanishing hypotheses.
-/

open CategoryTheory AlgebraicGeometry Order
open PrincipalFamilyUnitOpen PrincipalFamilyEndpointCuts
open Scheme.SmoothSite Scheme.SmoothSite.Contraction

universe u v

noncomputable section

example {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (n : R) :
    Module.length R (R ⧸ (RingHom.ker φ ⊔ Ideal.span {n})) =
      Module.length S (S ⧸ Ideal.span {φ n}) :=
  Module.quotient_length_ker_sup_span φ hφ n

variable {k : Type u} [Field k]

example (X : Scheme.SmoothSite (Spec (.of k))) (a : k) :
    (nativeAffineSection (.of k) X a).left ≫
      (affineCylinderPolynomialIso (.of k) X).hom.left = endpoint X.hom a :=
  nativeAffineSection_polynomialCylinder X a

example {W : Scheme.{u}} (p : W ⟶ Spec (.of k)) (a b : Γ(W, ⊤)) (x : W) :
    signedCutCoefficient p a b 0 x = 0 := signedCutCoefficient_zero p a b x

example {W : Scheme.{u}} [IsIntegral W] [IsNoetherian W]
    (p : W ⟶ Spec (.of k)) (a b : Γ(W, ⊤)) (x : W) (hx : coheight x = 1)
    (ha : W.presheaf.germ ⊤ x (by trivial) a ≠ 0)
    (hb : W.presheaf.germ ⊤ x (by trivial) b ≠ 0) :
    signedCutCoefficient p a b 1 x =
      W.ord (algebraMap (W.presheaf.stalk x) W.functionField
          (W.presheaf.germ ⊤ x (by trivial) a) /
        algebraMap (W.presheaf.stalk x) W.functionField
          (W.presheaf.germ ⊤ x (by trivial) b)) x :=
  signedCutCoefficient_one p a b x hx ha hb

#print axioms Module.quotient_length_ker_sup_span
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.graph_nativeAffineSection_comp
#print axioms AlgebraicGeometry.PrincipalFamilyEndpointCuts.endpoint_cut_finite
#print axioms AlgebraicGeometry.PrincipalFamilyEndpointCuts.signedCutCoefficient_one
