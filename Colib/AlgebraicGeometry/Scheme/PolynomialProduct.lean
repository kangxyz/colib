/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.Ring.PolynomialPushout

/-! # The actual polynomial spectrum and its base-change square

Extracted from https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/Motivic/Aglib/AlgebraicGeometry/EffectiveCartierDivisor/CoordinateGraphIdeal.lean
Source blob: 7fd6f091580be9b2b018f3d9138bb8fbb8ca26ed. Only the geometric product interface is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable (R : Type u) [CommRing R] {B : Type u} [CommRing B]

/-- The native polynomial spectrum is the actual affine-line product over the base ring. -/
def coordinateProductIso (f : R →+* B) :
    Spec (.of B[X]) ≅ CategoryTheory.Limits.pullback
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))
      (Spec.map (CommRingCat.ofHom f)) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.polynomial_isPushout (CommRingCat.ofHom f))).flip.isoPullback

@[reassoc (attr := simp)] theorem coordinateProductIso_hom_fst (f : R →+* B) :
    (coordinateProductIso R f).hom ≫ CategoryTheory.Limits.pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.polynomial_isPushout
      (CommRingCat.ofHom f))).flip.isoPullback_hom_fst

@[reassoc (attr := simp)] theorem coordinateProductIso_hom_snd (f : R →+* B) :
    (coordinateProductIso R f).hom ≫ CategoryTheory.Limits.pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* B[X])) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.polynomial_isPushout
      (CommRingCat.ofHom f))).flip.isoPullback_hom_snd


end AlgebraicGeometry.Scheme.Hom
