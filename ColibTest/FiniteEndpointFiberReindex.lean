/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.FiniteEndpointFiberReindex

/-! # Original endpoint/source-fibre and residue-degree regression -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Polynomial

attribute [local instance] Classical.propDecidable

universe u

namespace AlgebraicGeometry.Scheme.FiniteDominantFace

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  {C D E F : Scheme.{u}} [IsIntegral C]
  (f : C ⟶ Spec (.of A[X])) [IsFinite f] [IsDominant f]
  (e : E ⟶ C) (b : E ⟶ Spec (.of A)) (a : A)
  (hsq : IsPullback e b f (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))))
  (q : F ⟶ Spec (.of A)) [IsFinite q]
  (j : C ⟶ D) [IsFinite j] (i : F ⟶ D) [IsClosedImmersion i]
  (r : E ⟶ F) (hr : r ≫ q = b) (hcart : IsPullback e r j i)

include hsq hr hcart in
example {Y : Scheme.{u}} (g : F ⟶ Y)
    (L : C → ℤ) (y : Y) :
    (∑ᶠ x : genericPoints E,
      if g (r x.val) = y then L (e x.val) * ((r ≫ g).residueDegree x.val : ℤ) else 0) =
    ∑ᶠ z : (Σ t : genericPoints F, {x : C // j x = i t.val}),
      if g z.1.val = y then L z.2.val *
        ((j.residueDegree z.2.val : ℤ) * (g.residueDegree z.1.val : ℤ)) else 0 :=
  finsum_endpoint_source_fibres f e b a hsq q j i r hr hcart g L y

end AlgebraicGeometry.Scheme.FiniteDominantFace

#print axioms AlgebraicGeometry.Scheme.FiniteDominantFace.genericEndpointFiberMap_bijective

#print axioms AlgebraicGeometry.Scheme.FiniteDominantFace.genericEndpointFiberEquiv

#print axioms AlgebraicGeometry.Scheme.FiniteDominantFace.endpoint_residueDegree

#print axioms AlgebraicGeometry.Scheme.FiniteDominantFace.finsum_endpoint_source_fibres
