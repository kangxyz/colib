/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.PolynomialAlgebra

/-! # The actual polynomial base-change pushout

Uses Mathlib's native algebra pushout instance, with the supplied coefficient map.
This is the lower polynomial-square interface used by Cartier chart comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace CommRingCat

/-- Base change of the polynomial ring retains the specified coefficient ring homomorphism. -/
theorem polynomial_isPushout {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsPushout f (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
      (CommRingCat.ofHom (Polynomial.C : S →+* Polynomial S))
      (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) := by
  algebraize [f.hom, Polynomial.mapRingHom f.hom]
  exact CommRingCat.isPushout_of_isPushout R S (Polynomial R) (Polynomial S)

end CommRingCat
