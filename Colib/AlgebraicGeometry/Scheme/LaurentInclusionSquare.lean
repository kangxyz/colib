/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.LaurentCoordinateNaturality

/-! # The actual Laurent coefficient inclusion square

The constant Laurent inclusion commutes with every coefficient map.
-/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.PolynomialLaurent

/-- The actual constant-coefficient inclusion into the Laurent polynomial ring. -/
def laurentCoefficientInclusion (R : CommRingCat.{u}) :
    R ⟶ CommRingCat.of (LaurentPolynomial R) :=
  CommRingCat.ofHom LaurentPolynomial.C

/-- Laurent coefficient extension commutes with the actual constant inclusion. -/
theorem laurentCoefficientInclusion_square {R S : CommRingCat.{u}} (f : R ⟶ S) :
    laurentCoefficientInclusion R ≫ laurentCoefficientMap f =
      f ≫ laurentCoefficientInclusion S := by
  ext r : 2
  change AddMonoidAlgebra.mapRingHom ℤ f.hom (AddMonoidAlgebra.single 0 r) =
    AddMonoidAlgebra.single 0 (f.hom r)
  exact AddMonoidAlgebra.mapRingHom_single _ _ _

end AlgebraicGeometry.Scheme.PolynomialLaurent
