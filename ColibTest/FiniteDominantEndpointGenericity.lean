/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.FiniteDominantEndpointGenericity

/-! # Original finite dominant evaluation-fibre genericity regression -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.FiniteDominantFace

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  {C : Scheme.{u}} [IsIntegral C]
  (f : C ⟶ Spec (.of A[X])) [IsFinite f] [IsDominant f]

example
    {E F : Scheme.{u}} (e : E ⟶ C) (b : E ⟶ Spec (.of A)) (a : A)
    (hsq : IsPullback e b f
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))))
    (q : F ⟶ Spec (.of A)) [IsFinite q] (r : E ⟶ F) (hr : r ≫ q = b)
    (x : E) (hx : x ∈ genericPoints E) : r x ∈ genericPoints F :=
  original_face_generic_image_generic f e b a hsq q r hr x hx

end AlgebraicGeometry.Scheme.FiniteDominantFace

#print axioms Ideal.under_mem_minimalPrimes_of_hasGoingDown

#print axioms Ideal.comap_eq_of_mem_minimalPrimes_map_prime

#print axioms AlgebraicGeometry.Scheme.Hom.mem_genericPoints_of_image_generic

#print axioms AlgebraicGeometry.Scheme.Hom.genericFiberEquiv

#print axioms AlgebraicGeometry.Scheme.FiniteDominantFace.original_face_generic_over_zero

#print axioms AlgebraicGeometry.Scheme.FiniteDominantFace.original_face_generic_image_generic
