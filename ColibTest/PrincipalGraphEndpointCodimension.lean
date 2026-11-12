/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.GraphEndpointCodimension

/-! # Actual graph-incidence endpoint codimension regression -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.PrincipalFamilyUnitOpen Stacks.Chow

universe u

variable {k : Type u} [Field k] {X Z : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))

/-- Actual generic incidence points, without a support flatness premise. -/
example [IsIntegral X] [IsSeparated p]
    (c : k) (s : genericPoints X)
    (w : pullback (C := Scheme) (projection p ≫ p) h)
    [IsLocallyNoetherian (integralComponentAt w).subscheme]
    [IsDominant ((integralComponentAt w).subschemeι ≫ pullback.fst (projection p ≫ p) h ≫
      pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))]
    (x : genericPoints (correspondenceIncidence p (projection p ≫ p) h
      (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val) w)) :
    Order.coheight (pullback.snd (C := Scheme) _ _ x.val) = 1 :=
  graphIncidence_endpoint_generic_coheight p h c s w x

#print axioms AlgebraicGeometry.Scheme.Hom.coheight_eq_one_of_effective_kernel
#print axioms Stacks.Chow.PolynomialEndpointFiber.fiberInclusion_ker_isEffectiveCartierDivisor
#print axioms Stacks.Chow.PolynomialEndpointFiber.fiberInclusion_generic_coheight
#print axioms Stacks.Chow.graphFiber_endpoint_parameter_isPullback
#print axioms Stacks.Chow.graphFiber_endpoint_generic_coheight
#print axioms Stacks.Chow.graphIncidence_endpoint_generic_coheight
