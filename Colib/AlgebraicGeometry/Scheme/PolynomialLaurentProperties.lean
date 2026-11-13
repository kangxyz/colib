/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentProjection
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Flat.Localization

/-! # Flat coefficient projections and the inverted principal-open chart

Original proofs: Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/Basic.lean,
revision 2c34f185fa859e862661f939cd216b07bcccfb26, lines 41-46, 62-66, 122-129.
-/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.PolynomialLaurent
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/Basic.lean:41"
  "adaptation" "Original native maps, full-subcategory lifts and chart equations."]
instance instFlatLaurentProjection (R : CommRingCat.{u}) : Flat (laurentProjection R) := by
  apply Flat.SpecMap_iff.mpr
  change (algebraMap R (LaurentPolynomial R)).Flat
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/Basic.lean:62"
  "adaptation" "Original native maps, full-subcategory lifts and chart equations."]
instance instFlatPolynomialProjection (R : CommRingCat.{u}) : Flat (polynomialProjection R) := by
  apply Flat.SpecMap_iff.mpr
  change (algebraMap R (Polynomial R)).Flat
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/Basic.lean:122"
  "adaptation" "Original native maps, full-subcategory lifts and chart equations."]
instance instIsOpenImmersionLaurentMinus (R : CommRingCat.{u}) : IsOpenImmersion (laurentMinus R) :=
  by
  let e : CommRingCat.of (LaurentPolynomial R) ≅ CommRingCat.of (LaurentPolynomial R) :=
    (LaurentPolynomial.invert (R := R)).toRingEquiv.toCommRingCatIso
  unfold laurentMinus
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  change IsOpenImmersion (Spec.map e.hom ≫ laurentToPolynomial R)
  infer_instance
end AlgebraicGeometry.Scheme.PolynomialLaurent
