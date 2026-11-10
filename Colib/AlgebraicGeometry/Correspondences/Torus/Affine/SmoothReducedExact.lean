/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.SpecSectionsExact
public import Colib.RingTheory.Smooth.IntegrallyClosed

/-!
# Original smooth integral affine scope of the reduced divisor sequence

Only a field, a smooth algebra, and its integrality are required. Native
smooth normality supplies integral closure, and finite type supplies
Noetherianness. The coefficient algebra need not be a field, factorial,
finite dimensional, or geometrically integral. The coefficients are the
actual global boundary-one and ordinary unit presheaves.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- The original structure map of the affine smooth algebra. -/
abbrev smoothAffineStructure : Spec (.of R) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k R))

private instance smoothAffineStructure_smooth : Smooth (smoothAffineStructure k R) := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact (RingHom.smooth_algebraMap).mpr inferInstance

variable [IsDomain R]

/-- The actual original-coefficient sequence for a smooth integral affine algebra. -/
def smoothAffineReducedDivisorShortComplex : ShortComplex AddCommGrpCat.{u + 1} := by
  letI : Smooth (smoothAffineStructure k R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact (RingHom.smooth_algebraMap).mpr inferInstance
  letI : IsIntegrallyClosed R := Algebra.Smooth.isIntegrallyClosed_of_field k R
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  exact specSectionsReducedDivisorShortComplex (smoothAffineStructure k R)

/-- The actual affine sequence is short exact over every field, with no extra norm premises. -/
theorem smoothAffineReducedDivisorShortComplex_shortExact :
    (smoothAffineReducedDivisorShortComplex k R).ShortExact := by
  have : IsIntegrallyClosed R := Algebra.Smooth.isIntegrallyClosed_of_field k R
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  exact specSectionsReducedDivisorShortComplex_shortExact (smoothAffineStructure k R)

end AlgebraicGeometry.NativeTorusPolynomial
