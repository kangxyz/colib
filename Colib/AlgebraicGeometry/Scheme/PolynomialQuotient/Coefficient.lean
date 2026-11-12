/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.Basic
public import Colib.AlgebraicGeometry.BaseChange.Affine.AdjoinRootBaseChange
public import Mathlib.RingTheory.Polynomial.Quotient
/-! # Literal source, target and whole-fiber coordinates of polynomial quotients -/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Spec/PolynomialQuotient/PolynomialQuotientCoordinates.lean`, blob
`807d29ce5848922f60cd65075c194d31bdadcbb1`.
The source is the actual original scheme or ordinary free-Yoneda Ext group.
All monic quotient fibers retain their full scheme structure.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient
variable {k R : Type u} [CommRing k] [CommRing R] (σ : k →+* R)

variable {S : Type u} [CommRing S] (φ : R →+* S) (p : R[X])

/-- Literal whole quotient base change, including nonreduced fibers. -/
def coefficientMap : Spec (.of (AdjoinRoot (p.map φ))) ⟶ Spec (.of (AdjoinRoot p)) :=
  Spec.map (CommRingCat.ofHom (AdjoinRoot.map φ p (p.map φ) dvd_rfl))

theorem coefficient_isPullback :
    IsPullback (source (p.map φ)) (coefficientMap φ p)
      (Spec.map (CommRingCat.ofHom φ)) (source p) :=
  AdjoinRootBaseChange.isPullback φ p

end AlgebraicGeometry.PolynomialOpenQuotient
