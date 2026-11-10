/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Polynomial.LaurentUnderSquare
import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.AffineBaseChange

/-! The fixed-open pullbacks use the original Under arrows, contravariantly and strictly. -/
noncomputable section
open CategoryTheory AlgebraicGeometry CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
variable (a : Under R)

example : openSpace j ((polynomialUnderFunctor R).obj a) =
    Limits.pullback j (Spec.map (a.hom ≫ CommRingCat.ofHom Polynomial.C)) := rfl
example : openSpace j ((laurentUnderFunctor R).obj a) =
    Limits.pullback j (Spec.map (a.hom ≫ CommRingCat.ofHom LaurentPolynomial.C)) := rfl
example : openMap j ((polynomialUnderCoefficient R).app a) ≫ inclusion j a =
    inclusion j ((polynomialUnderFunctor R).obj a) ≫
      Spec.map (CommRingCat.ofHom Polynomial.C) := openMap_inclusion _ _
example : openMap j ((laurentUnderCoefficient R).app a) ≫ inclusion j a =
    inclusion j ((laurentUnderFunctor R).obj a) ≫
      Spec.map (CommRingCat.ofHom LaurentPolynomial.C) := openMap_inclusion _ _
example : openMap j ((underToLaurent R).app a) ≫
    inclusion j ((polynomialUnderFunctor R).obj a) =
      inclusion j ((laurentUnderFunctor R).obj a) ≫
        Spec.map (CommRingCat.ofHom Polynomial.toLaurent) := openMap_inclusion _ _
example : openMap j ((underToLaurentInvert R).app a) ≫
    inclusion j ((polynomialUnderFunctor R).obj a) =
      inclusion j ((laurentUnderFunctor R).obj a) ≫ Spec.map
        (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)) :=
  openMap_inclusion _ _

example : openMap j ((underToLaurent R).app a) ≫
    openMap j ((polynomialUnderCoefficient R).app a) =
      openMap j ((laurentUnderCoefficient R).app a) := by
  rw [← openMap_comp, polynomialUnderCoefficient_toLaurent]
example : openMap j ((underToLaurentInvert R).app a) ≫
    openMap j ((polynomialUnderCoefficient R).app a) =
      openMap j ((laurentUnderCoefficient R).app a) := by
  rw [← openMap_comp, polynomialUnderCoefficient_toLaurentInvert]
example : openMap j ((underToLaurent R).app a) ≫
    openMap j ((polynomialUnderCoefficient R).app a) =
      openMap j ((underToLaurentInvert R).app a) ≫
        openMap j ((polynomialUnderCoefficient R).app a) := by
  rw [← openMap_comp, ← openMap_comp, polynomialUnderCoefficient_toLaurent,
    polynomialUnderCoefficient_toLaurentInvert]

variable {a} {b c : Under R} (f : a ⟶ b) (g : b ⟶ c)
example : openMap j ((laurentUnderFunctor R).map f) ≫
    inclusion j ((laurentUnderFunctor R).obj a) =
      inclusion j ((laurentUnderFunctor R).obj b) ≫
        Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f.right.hom)) :=
  openMap_inclusion _ _
example : openMap j ((laurentUnderFunctor R).map (f ≫ g)) =
    openMap j ((laurentUnderFunctor R).map g) ≫
      openMap j ((laurentUnderFunctor R).map f) := by
  rw [Functor.map_comp, openMap_comp]
example : openMap j ((underToLaurent R).app b) ≫
    openMap j ((polynomialUnderFunctor R).map f) =
      openMap j ((laurentUnderFunctor R).map f) ≫ openMap j ((underToLaurent R).app a) := by
  rw [← openMap_comp, ← openMap_comp, NatTrans.naturality]

-- The identity algebra still has the actual chosen pullback, with the specified projection iso.
example : (identityProjectionIso j).hom ≫ j = inclusion j (Under.mk (𝟙 R)) :=
  identityProjectionIso_inclusion j
