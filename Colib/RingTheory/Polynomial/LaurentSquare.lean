/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# The two-chart polynomial and Laurent square

The right vertical chart sends `X` to `T 1`; the bottom horizontal chart sends it to `T (-1)`.
All four coefficient maps are the canonical Mathlib ring homomorphisms, for arbitrary rings,
including the zero ring. No flatness hypothesis is used.

Implementation provenance: the polynomial and Laurent square in
`Aglib/Algebra/Polynomial/Laurent/Square.lean` and its coefficient identities in `BaseChange.lean`
at `2c34f185fa859e862661f939cd216b07bcccfb26`.
-/
@[expose] public section

noncomputable section
open CategoryTheory
universe u
namespace CommRingCat.PolynomialLaurent

/-- Both coefficient legs followed by the positive chart are the Laurent inclusion. -/
theorem coefficient_toLaurent (R : CommRingCat.{u}) :
    CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
        CommRingCat.ofHom Polynomial.toLaurent = CommRingCat.ofHom LaurentPolynomial.C := by
  apply CommRingCat.hom_ext
  exact RingHom.ext Polynomial.toLaurent_C

/-- Inversion fixes the coefficient inclusion. -/
theorem coefficient_toLaurent_invert (R : CommRingCat.{u}) :
    CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
        CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) =
      CommRingCat.ofHom LaurentPolynomial.C := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (congrArg LaurentPolynomial.invert (Polynomial.toLaurent_C r)).trans
    (LaurentPolynomial.invert_C r)

/-- Polynomial coefficient extension commutes with constants. -/
theorem polynomial_coefficient_square {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f ≫ CommRingCat.ofHom Polynomial.C =
      CommRingCat.ofHom Polynomial.C ≫ CommRingCat.ofHom (Polynomial.mapRingHom f.hom) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (Polynomial.map_C f.hom).symm

/-- Coefficient extension retains the positive Laurent chart. -/
theorem toLaurent_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    CommRingCat.ofHom (Polynomial.mapRingHom f.hom) ≫
        CommRingCat.ofHom Polynomial.toLaurent =
      CommRingCat.ofHom Polynomial.toLaurent ≫
        CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f.hom) := by
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change Polynomial.toLaurent (Polynomial.map f.hom (Polynomial.C r)) =
      AddMonoidAlgebra.mapRingHom ℤ f.hom (Polynomial.toLaurent (Polynomial.C r))
    rw [Polynomial.map_C, Polynomial.toLaurent_C, Polynomial.toLaurent_C]
    exact (AddMonoidAlgebra.mapRingHom_single f.hom 0 r).symm
  · change Polynomial.toLaurent (Polynomial.map f.hom Polynomial.X) =
      AddMonoidAlgebra.mapRingHom ℤ f.hom (Polynomial.toLaurent Polynomial.X)
    rw [Polynomial.map_X, Polynomial.toLaurent_X, Polynomial.toLaurent_X]
    change AddMonoidAlgebra.single 1 (1 : S) =
      AddMonoidAlgebra.mapRingHom ℤ f.hom (AddMonoidAlgebra.single 1 1)
    rw [AddMonoidAlgebra.mapRingHom_single, map_one]

/-- Coefficient extension commutes with exponent inversion, not additive negation. -/
theorem invert_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f.hom) ≫
        CommRingCat.ofHom LaurentPolynomial.invert.toRingHom =
      CommRingCat.ofHom LaurentPolynomial.invert.toRingHom ≫
        CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f.hom) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  apply LaurentPolynomial.ext
  intro k
  simp

/-- Coefficient extension retains the inverse Laurent chart. -/
theorem inverseChart_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    CommRingCat.ofHom (Polynomial.mapRingHom f.hom) ≫
        CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) =
      CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) ≫
        CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f.hom) := by
  change (CommRingCat.ofHom (Polynomial.mapRingHom f.hom) ≫
      CommRingCat.ofHom Polynomial.toLaurent) ≫
      CommRingCat.ofHom LaurentPolynomial.invert.toRingHom =
    CommRingCat.ofHom Polynomial.toLaurent ≫
      (CommRingCat.ofHom LaurentPolynomial.invert.toRingHom ≫
        CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f.hom))
  rw [toLaurent_naturality, Category.assoc, invert_naturality]

/-- The strict square with positive right chart and inverse bottom chart. -/
def laurentSquare (R : CommRingCat.{u}) : Arrow (Arrow CommRingCat.{u}) :=
  Arrow.mk (Arrow.homMk
    (f := Arrow.mk (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
    (g := Arrow.mk (CommRingCat.ofHom
      (LaurentPolynomial.invert.toRingHom.comp (Polynomial.toLaurent (R := R)))))
    (CommRingCat.ofHom Polynomial.C) (CommRingCat.ofHom Polynomial.toLaurent)
    (by
      exact (coefficient_toLaurent_invert R).trans (coefficient_toLaurent R).symm))

/-- The four coefficient components are `f`, `Polynomial.map f`, `Polynomial.map f`, and
`AddMonoidAlgebra.mapRingHom ℤ f`. -/
def laurentSquareMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    laurentSquare R ⟶ laurentSquare S :=
  Arrow.homMk
    (Arrow.homMk f (CommRingCat.ofHom (Polynomial.mapRingHom f.hom))
      (polynomial_coefficient_square f))
    (Arrow.homMk (CommRingCat.ofHom (Polynomial.mapRingHom f.hom))
      (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f.hom))
      (inverseChart_naturality f))
    (by
      apply Arrow.hom_ext
      · exact polynomial_coefficient_square f
      · exact toLaurent_naturality f)

/-- The actual two-chart square is strictly functorial in every coefficient ring. -/
def laurentSquareFunctor : CommRingCat.{u} ⥤ Arrow (Arrow CommRingCat.{u}) where
  obj := laurentSquare
  map := laurentSquareMap
  map_id R := by
    apply Arrow.hom_ext <;> apply Arrow.hom_ext <;> apply CommRingCat.hom_ext
    · rfl
    · exact Polynomial.mapRingHom_id
    · exact Polynomial.mapRingHom_id
    · exact AddMonoidAlgebra.mapRingHom_id
  map_comp f g := by
    apply Arrow.hom_ext <;> apply Arrow.hom_ext <;> apply CommRingCat.hom_ext
    · rfl
    · exact (Polynomial.mapRingHom_comp g.hom f.hom).symm
    · exact (Polynomial.mapRingHom_comp g.hom f.hom).symm
    · exact AddMonoidAlgebra.mapRingHom_comp g.hom f.hom

end CommRingCat.PolynomialLaurent

attribute [colib_ref "aglib"
  "Aglib/Algebra/Polynomial/Laurent/Square.lean:40-101" "adaptation"
  "Canonical two-chart ring square, strict coefficient functor, and literal constant composites"]
  CommRingCat.PolynomialLaurent.laurentSquare
  CommRingCat.PolynomialLaurent.laurentSquareMap
  CommRingCat.PolynomialLaurent.laurentSquareFunctor
  CommRingCat.PolynomialLaurent.coefficient_toLaurent
  CommRingCat.PolynomialLaurent.coefficient_toLaurent_invert
