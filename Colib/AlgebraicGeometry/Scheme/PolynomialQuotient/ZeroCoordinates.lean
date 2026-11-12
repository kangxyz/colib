/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.Basic
public import Mathlib.RingTheory.Polynomial.Quotient

/-! # Whole linear-quotient coordinates

These are the original AdjoinRoot structural map and literal evaluation map.
No reduced support, rational point or replacement zero is used.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient
variable {R : Type u} [CommRing R]

/-- The exact linear quotient structural map is an isomorphism. -/
instance source_linear_isIso (a : R) : IsIso (source (X - C a)) := by
  have he : CommRingCat.ofHom (AdjoinRoot.of (X - C a)) =
      (quotientSpanXSubCAlgEquiv a).toRingEquiv.toCommRingCatIso.inv := by
    ext r
    exact (quotientSpanXSubCAlgEquiv_symm_apply a r).symm
  unfold source
  rw [he]
  infer_instance

end AlgebraicGeometry.PolynomialOpenQuotient
