/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialEndpointFiberMap

/-! # Original polynomial endpoint and both finite residue-factor regression -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance] Classical.propDecidable

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

example
    {k : Type u} [Field k] {X C D Y : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsAffine X] [IsIntegral X] [Smooth p]
    (n : D ⟶ parameterSpace p) [IsFinite n]
    (j : C ⟶ D) [IsFinite j] [IsIntegral C] [IsDominant (j ≫ n)] (c : k)
    (g : pullback (endpoint p c) n ⟶ Y) (L : C → ℤ) (y : Y) :
    (∑ᶠ x : genericPoints (pullback (C := Scheme) (endpoint p c) (j ≫ n)),
      if g (polynomialEndpointMap p n j c x.val) = y then
        L (pullback.snd (endpoint p c) (j ≫ n) x.val) *
          ((polynomialEndpointMap p n j c ≫ g).residueDegree x.val : ℤ) else 0) =
    ∑ᶠ z : (Σ t : genericPoints (pullback (C := Scheme) (endpoint p c) n),
      {x : C // j x = pullback.snd (endpoint p c) n t.val}),
      if g z.1.val = y then L z.2.val *
        ((j.residueDegree z.2.val : ℤ) * (g.residueDegree z.1.val : ℤ)) else 0 :=
  polynomialEndpoint_finsum_source_fibres p n j c g L y

end AlgebraicGeometry.PrincipalFamilyUnitOpen

#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.affinePolynomialIso

#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.affinePolynomialIso_endpoint

#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.affinePolynomialIso_endpoint_isPullback

#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.polynomialEndpoint_coordinate_isPullback

#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.polynomialEndpoint_generic_image_generic_of_smooth

#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.polynomialEndpointMap_isPullback

#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.polynomialEndpoint_finsum_source_fibres
