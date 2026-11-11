/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.Scheme.CoefficientBaseChange
public import Colib.AlgebraicGeometry.Scheme.IntegerBaseProducts
public import Colib.RingTheory.Polynomial.LaurentUnderSquare

/-! # Original integral Spec and coefficient comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.Products
universe u


namespace AlgebraicGeometry.Scheme.BaseChange.Coefficients
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- Original native coefficient reindexing as a scheme map. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:42"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
def coefficientMap {a b : Under R} (g : a ⟶ b) : space (op P, b) ⟶ space (op P, a) :=
  map (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)

/-- Its square with the actual coefficient projections is cartesian. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:46"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem coefficientMap_isPullback {a b : Under R} (g : a ⟶ b) :
    IsPullback (coefficientMap P g) (coefficientProjection (op P, b))
      (coefficientProjection (op P, a)) (Spec.map g.right) := by
  apply IsPullback.of_right (h₁₂ := projection (op P, a)) (h₂₂ := Spec.map a.hom)
  · have hp : coefficientMap P g ≫ projection (op P, a) = projection (op P, b) := by
      rw [coefficientMap, map_projection]
      exact Category.comp_id _
    rw [hp, ← Spec.map_comp, Under.w g]
    exact IsPullback.of_hasPullback P.hom (Spec.map b.hom)
  · exact map_coefficientProjection (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)
  · exact IsPullback.of_hasPullback P.hom (Spec.map a.hom)

/-- Original native coefficient maps compose on the same fixed fibers. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:59"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem coefficientMap_comp {a b c : Under R} (g : a ⟶ b) (h : b ⟶ c) :
    coefficientMap P (g ≫ h) = coefficientMap P h ≫ coefficientMap P g := by
  have hc := map_comp (i := (op P, a)) (k := (op P, b)) (l := (op P, c))
    (𝟙 (op P), g) (𝟙 (op P), h)
  change map (i := (op P, a)) (k := (op P, c))
    (𝟙 (op P) ≫ 𝟙 (op P), g ≫ h) = _ at hc
  simpa only [Category.id_comp, coefficientMap] using hc

/-- Every coefficient arrow retains the original native coefficient projection square. -/
@[reassoc,
  colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:68"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
theorem coefficientMap_coefficientProjection {a b : Under R} (g : a ⟶ b) :
    coefficientMap P g ≫ coefficientProjection (op P, a) =
      coefficientProjection (op P, b) ≫ Spec.map g.right :=
  map_coefficientProjection (i := (op P, a)) (k := (op P, b)) (𝟙 (op P), g)

/-- Original projection from the fixed Laurent coefficient fiber. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:83"
  "adaptation" "Original whole Spec row, both projections, charts and forward Laurent unit"]
def laurentProjection (a : Under R) :
    space (op P, (laurentUnderFunctor R).obj a) ⟶ space (op P, a) :=
  coefficientMap P ((laurentUnderCoefficient R).app a)


end AlgebraicGeometry.Scheme.BaseChange.Coefficients
