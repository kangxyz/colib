/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionUnitNaturality
public import Colib.AlgebraicGeometry.Scheme.LaurentCoordinateNaturality

/-!
# The original Laurent unit on the strict section model

The section automorphism comes from the original Laurent global unit. At every actual coefficient
arrow from the Laurent ring its scalar is the image of the original coordinate, with the original
inverse coordinate. Coefficient reindexing commutes strictly with this action. This is a categorical
action; no Bass seed or localization conclusion is asserted.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The strict Laurent section action lifts the original coordinate global unit. -/
@[colib_tag "COL-0359",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentUnit.lean:33-36"
    "adaptation" "Actual forward Laurent coordinate action on native cocartesian sections"]
def boundedAboveFlatAffineSectionLaurentUnitIso (R : CommRingCat.{u}) :
    𝟭 (BoundedAboveFlatAffineSections (.of (LaurentPolynomial R))) ≅
      𝟭 (BoundedAboveFlatAffineSections (.of (LaurentPolynomial R))) :=
  boundedAboveFlatAffineSectionUnitIso (.of (LaurentPolynomial R)) (laurentCoordinate R)

/-- Every original coefficient arrow retains the actual pulled-back Laurent-unit automorphism. -/
theorem boundedAboveFlatAffineSectionLaurentUnitIso_evaluation {R S : CommRingCat.{u}}
    (h : CommRingCat.of (LaurentPolynomial R) ⟶ S)
    (s : BoundedAboveFlatAffineSections (.of (LaurentPolynomial R))) :
    (boundedAboveFlatAffineEvaluationAt (.of (LaurentPolynomial R)) (Under.mk h)).mapIso
        ((boundedAboveFlatAffineSectionLaurentUnitIso R).app s) =
      (boundedAboveFlatPerfectGlobalUnitIso (Spec S)
        (Units.map (Spec.map h).appTop.hom.toMonoidHom (laurentCoordinate R))).app
          ((boundedAboveFlatAffineEvaluationAt (.of (LaurentPolynomial R)) (Under.mk h)).obj s) :=
  boundedAboveFlatAffineEvaluationAt_mapIso_sectionUnitIso _ _ s (Under.mk h)

/-- Actual Laurent coefficient restriction commutes strictly with the original unit action. -/
theorem boundedAboveFlatAffineSectionLaurentUnitIso_coefficient
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Functor.whiskerRight (boundedAboveFlatAffineSectionLaurentUnitIso R).hom
        (boundedAboveFlatAffineSectionsMap (laurentCoefficientMap f)) =
      Functor.whiskerLeft (boundedAboveFlatAffineSectionsMap (laurentCoefficientMap f))
        (boundedAboveFlatAffineSectionLaurentUnitIso S).hom := by
  simpa only [boundedAboveFlatAffineSectionLaurentUnitIso, laurentCoordinate_coefficient] using
    boundedAboveFlatAffineSectionUnitIso_coefficient_hom
      (laurentCoefficientMap f) (laurentCoordinate R)

/-- The whole Laurent unit isomorphism is strictly natural in the coefficient ring. -/
theorem boundedAboveFlatAffineSectionLaurentUnitIso_coefficient_iso
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Functor.isoWhiskerRight (boundedAboveFlatAffineSectionLaurentUnitIso R)
        (boundedAboveFlatAffineSectionsMap (laurentCoefficientMap f)) =
      Functor.isoWhiskerLeft (boundedAboveFlatAffineSectionsMap (laurentCoefficientMap f))
        (boundedAboveFlatAffineSectionLaurentUnitIso S) := by
  apply Iso.ext
  exact boundedAboveFlatAffineSectionLaurentUnitIso_coefficient f

/-- The inverse Laurent unit is strictly natural under actual coefficient reindexing. -/
theorem boundedAboveFlatAffineSectionLaurentUnitIso_coefficient_inv
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Functor.whiskerRight (boundedAboveFlatAffineSectionLaurentUnitIso R).inv
        (boundedAboveFlatAffineSectionsMap (laurentCoefficientMap f)) =
      Functor.whiskerLeft (boundedAboveFlatAffineSectionsMap (laurentCoefficientMap f))
        (boundedAboveFlatAffineSectionLaurentUnitIso S).inv :=
  congrArg Iso.inv (boundedAboveFlatAffineSectionLaurentUnitIso_coefficient_iso f)

/-- The forward action on every original complex term multiplies by the actual image of T. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentUnit.lean:59-76"
  "adaptation" "Forward term formula for an arbitrary Laurent ring morphism"]
theorem boundedAboveFlatAffineSectionLaurentUnitIso_hom_terms {R S : CommRingCat.{u}}
    (h : CommRingCat.of (LaurentPolynomial R) ⟶ S)
    (s : BoundedAboveFlatAffineSections (.of (LaurentPolynomial R))) (n : ℤ) :
    ((boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι.map
      ((boundedAboveFlatAffineEvaluationAt (.of (LaurentPolynomial R)) (Under.mk h)).map
        ((boundedAboveFlatAffineSectionLaurentUnitIso R).hom.app s))).f n =
      (Stacks.RegularSequence.globalSmulCenter (Spec S)
        ((Scheme.ΓSpecIso S).inv (h.hom (LaurentPolynomial.T 1)))).app
          (((boundedAboveFlatAffineEvaluationAt (.of (LaurentPolynomial R))
            (Under.mk h)).obj s).obj.X n) := by
  rw [boundedAboveFlatAffineSectionLaurentUnitIso,
    boundedAboveFlatAffineEvaluationAt_map_sectionUnitIso_hom]
  dsimp only [Under.mk, Under.right, Under.hom, StructuredArrow.mk]
  rw [boundedAboveFlatPerfectGlobalUnitIso_hom_terms, laurentCoordinate_image]

/-- The inverse action on every original complex term multiplies by the image of T inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentUnit.lean:79-95"
  "adaptation" "Inverse term formula for an arbitrary Laurent ring morphism"]
theorem boundedAboveFlatAffineSectionLaurentUnitIso_inv_terms {R S : CommRingCat.{u}}
    (h : CommRingCat.of (LaurentPolynomial R) ⟶ S)
    (s : BoundedAboveFlatAffineSections (.of (LaurentPolynomial R))) (n : ℤ) :
    ((boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι.map
      ((boundedAboveFlatAffineEvaluationAt (.of (LaurentPolynomial R)) (Under.mk h)).map
        ((boundedAboveFlatAffineSectionLaurentUnitIso R).inv.app s))).f n =
      (Stacks.RegularSequence.globalSmulCenter (Spec S)
        ((Scheme.ΓSpecIso S).inv (h.hom (LaurentPolynomial.T (-1))))).app
          (((boundedAboveFlatAffineEvaluationAt (.of (LaurentPolynomial R))
            (Under.mk h)).obj s).obj.X n) := by
  rw [boundedAboveFlatAffineSectionLaurentUnitIso,
    boundedAboveFlatAffineEvaluationAt_map_sectionUnitIso_inv]
  dsimp only [Under.mk, Under.right, Under.hom, StructuredArrow.mk]
  rw [boundedAboveFlatPerfectGlobalUnitIso_inv_terms]
  rw [laurentCoordinate_image_inv]

end AlgebraicGeometry.Scheme.Modules
