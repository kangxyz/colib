/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.Bertini.RelativePolynomialCoordinates

/-! # The unchanged relative coordinates as an algebra map -/
@[expose] public noncomputable section
open MvPolynomial
universe u
namespace QuadraticIncidence

/-- The canonical coordinate relabeling preserves the original scalar algebra. -/
def relativeCoordinateAlgHom (k B : Type u) [CommRing k] [CommRing B] [Algebra k B]
    (d : ℕ) (f : Fin (d + 1) → B) : Polynomial (MvPolynomial (Fin d) k) →ₐ[k] B :=
  (aeval f).comp (finSuccEquiv k d).symm.toAlgHom

/-- No new coordinate map is selected. -/
@[simp] theorem relativeCoordinateAlgHom_toRingHom
    (k B : Type u) [CommRing k] [CommRing B] [Algebra k B]
    (d : ℕ) (f : Fin (d + 1) → B) :
    (relativeCoordinateAlgHom k B d f : Polynomial (MvPolynomial (Fin d) k) →+* B) =
      relativeCoordinateHom k B d f := rfl

end QuadraticIncidence
