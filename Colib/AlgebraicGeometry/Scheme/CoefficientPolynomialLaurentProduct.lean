/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.CoefficientLaurentProjection
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentBaseChange
public import Colib.AlgebraicGeometry.Scheme.LaurentCoordinateNaturality

/-!
# Actual coefficient polynomial and Laurent products

The original two charts compare with the fixed products by genuine pullback isomorphisms.
Both projections and the forward Laurent unit are retained; chosen pullbacks are not equated.
Source: Aglib Coefficients/PolynomialLaurent.lean, revision
`2c34f185fa859e862661f939cd216b07bcccfb26`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
universe u
namespace AlgebraicGeometry.Scheme.BaseChange.Coefficients
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- All four original native corners and their actual geometric maps. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:74"
  "adaptation" "Actual coefficient product projections, oriented charts and original naturality."]
def laurentSquare (a : Under R) : Arrow (Arrow AlgebraicGeometry.Scheme.{u}ᵒᵖ) :=
  (row P ⋙ functor R).mapArrow.mapArrow.obj (laurentUnderSquare R a)

/-- Original positive-chart projection from the fixed polynomial coefficient fiber. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:78"
  "adaptation" "Actual coefficient product projections, oriented charts and original naturality."]
def polynomialProjection (a : Under R) :
    space (op P, (polynomialUnderFunctor R).obj a) ⟶ space (op P, a) :=
  coefficientMap P ((polynomialUnderCoefficient R).app a)

/-- The original positive-coordinate chart on the fixed native coefficient fibers. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:88"
  "adaptation" "Actual coefficient product projections, oriented charts and original naturality."]
def laurentPlus (a : Under R) :
    space (op P, (laurentUnderFunctor R).obj a) ⟶
      space (op P, (polynomialUnderFunctor R).obj a) :=
  coefficientMap P ((underToLaurent R).app a)

/-- The original inverse-coordinate chart; its source still carries the forward unit. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:94"
  "adaptation" "Actual coefficient product projections, oriented charts and original naturality."]
def laurentMinus (a : Under R) :
    space (op P, (laurentUnderFunctor R).obj a) ⟶
      space (op P, (polynomialUnderFunctor R).obj a) :=
  coefficientMap P ((underToLaurentInvert R).app a)

/-- Both original positive source legs have the same actual native coefficient composite. -/
@[reassoc, colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:100"
  "adaptation" "Actual coefficient product projections, oriented charts and original naturality."]
theorem laurentPlus_projection (a : Under R) :
    laurentPlus P a ≫ polynomialProjection P a = laurentProjection P a := by
  change coefficientMap P ((underToLaurent R).app a) ≫
    coefficientMap P ((polynomialUnderCoefficient R).app a) = _
  rw [← coefficientMap_comp, polynomialUnderCoefficient_toLaurent]
  rfl

/-- The original inverse chart has precisely that same actual native coefficient composite. -/
@[reassoc, colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:108"
  "adaptation" "Actual coefficient product projections, oriented charts and original naturality."]
theorem laurentMinus_projection (a : Under R) :
    laurentMinus P a ≫ polynomialProjection P a = laurentProjection P a := by
  change coefficientMap P ((underToLaurentInvert R).app a) ≫
    coefficientMap P ((polynomialUnderCoefficient R).app a) = _
  rw [← coefficientMap_comp, polynomialUnderCoefficient_toLaurentInvert]
  rfl

/-- The native polynomial fiber is the actual product over the common integral base. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:116"
  "adaptation" "Actual coefficient product projections, oriented charts and original naturality."]
theorem polynomial_isPullback (a : Under R) :
    IsPullback (polynomialProjection P a)
      (coefficientProjection (op P, (polynomialUnderFunctor R).obj a) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (integerMap a.right).hom)))
      (specULiftZIsTerminal.from (space (op P, a)))
      (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ))) := by
  have h := (coefficientMap_isPullback P ((polynomialUnderCoefficient R).app a)).paste_vert
    (PolynomialLaurent.Relative.polynomialSpec_isPullback a.right)
  simpa only [Functor.id_obj, specULiftZIsTerminal.comp_from, polynomialProjection] using h

/-- The native Laurent fiber is the actual product over the same integral base. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:127"
  "adaptation" "Actual coefficient product projections, oriented charts and original naturality."]
theorem laurent_isPullback (a : Under R) :
    IsPullback (laurentProjection P a)
      (coefficientProjection (op P, (laurentUnderFunctor R).obj a) ≫
        Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ (integerMap a.right).hom)))
      (specULiftZIsTerminal.from (space (op P, a)))
      (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u} ℤ))) := by
  have h := (coefficientMap_isPullback P ((laurentUnderCoefficient R).app a)).paste_vert
    (PolynomialLaurent.Relative.laurentSpec_isPullback a.right)
  simpa only [Functor.id_obj, specULiftZIsTerminal.comp_from, laurentProjection] using h

/-- Actual comparison with the specified polynomial product, preserving its projections. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:138"
  "adaptation" "Actual coefficient product projections, oriented charts and original naturality."]
def polynomialIso (a : Under R) :
    space (op P, (polynomialUnderFunctor R).obj a) ≅
      (baseProductFunctor (PolynomialLaurent.polynomialProjection
          (CommRingCat.of (ULift.{u} ℤ)))).obj
        (space (op P, a)) := (polynomial_isPullback P a).isoPullback

/-- Actual comparison with the specified Laurent product, preserving its projections. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:144"
  "adaptation" "Actual coefficient product projections, oriented charts and original naturality."]
def laurentIso (a : Under R) :
    space (op P, (laurentUnderFunctor R).obj a) ≅
      (baseProductFunctor (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u} ℤ)))).obj
        (space (op P, a)) := (laurent_isPullback P a).isoPullback

/-- The native polynomial comparison keeps the original source projection. -/
@[reassoc, colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:150"
  "adaptation" "Actual coefficient product projections, oriented charts and original naturality."]
theorem polynomialIso_hom_fst (a : Under R) :
    (polynomialIso P a).hom ≫ pullback.fst _ _ = polynomialProjection P a :=
  (polynomial_isPullback P a).isoPullback_hom_fst

/-- The native polynomial comparison keeps its exact integer coefficient leg. -/
@[reassoc, colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:155"
  "adaptation" "Actual coefficient product projections, oriented charts and original naturality."]
theorem polynomialIso_hom_snd (a : Under R) :
    (polynomialIso P a).hom ≫ pullback.snd _ _ =
      coefficientProjection (op P, (polynomialUnderFunctor R).obj a) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (integerMap a.right).hom)) :=
  (polynomial_isPullback P a).isoPullback_hom_snd

/-- The native Laurent comparison keeps the original source projection. -/
@[reassoc, colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:162"
  "adaptation" "Actual coefficient product projections, oriented charts and original naturality."]
theorem laurentIso_hom_fst (a : Under R) :
    (laurentIso P a).hom ≫ pullback.fst _ _ = laurentProjection P a :=
  (laurent_isPullback P a).isoPullback_hom_fst

/-- The native Laurent comparison keeps its exact integer coefficient leg. -/
@[reassoc, colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:167"
  "adaptation" "Actual coefficient product projections, oriented charts and original naturality."]
theorem laurentIso_hom_snd (a : Under R) :
    (laurentIso P a).hom ≫ pullback.snd _ _ =
      coefficientProjection (op P, (laurentUnderFunctor R).obj a) ≫
        Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ (integerMap a.right).hom)) :=
  (laurent_isPullback P a).isoPullback_hom_snd

/-- The actual positive chart agrees under the original native/product isomorphisms. -/
@[reassoc, colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:174"
  "adaptation" "Actual coefficient product projections, oriented charts and original naturality."]
theorem polynomialLaurentIso_plus (a : Under R) :
    laurentPlus P a ≫ (polynomialIso P a).hom =
      (laurentIso P a).hom ≫
        (baseProductTransformation _ _ (PolynomialLaurent.laurentToPolynomial
          (CommRingCat.of (ULift.{u} ℤ)))
          (PolynomialLaurent.laurentToPolynomial_projection
          (CommRingCat.of (ULift.{u} ℤ)))).app (space (op P, a)) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, polynomialIso_hom_fst, baseProductTransformation,
      pullback.lift_fst, Category.comp_id, laurentIso_hom_fst, laurentPlus_projection]
  · simp only [Category.assoc, polynomialIso_hom_snd, baseProductTransformation,
      pullback.lift_snd, laurentIso_hom_snd_assoc]
    change coefficientMap P ((underToLaurent R).app a) ≫
      coefficientProjection (op P, (polynomialUnderFunctor R).obj a) ≫ _ = _
    rw [coefficientMap_coefficientProjection_assoc]
    change coefficientProjection (op P, (laurentUnderFunctor R).obj a) ≫
      PolynomialLaurent.laurentToPolynomial a.right ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (integerMap a.right).hom)) = _
    rw [PolynomialLaurent.laurentToPolynomial, PolynomialLaurent.laurentToPolynomial,
      ← Spec.map_comp, ← Spec.map_comp, toLaurent_naturality]

/-- The inverse-coordinate chart agrees as well, retaining its original inversion. -/
@[reassoc, colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:193"
  "adaptation" "Actual coefficient product projections, oriented charts and original naturality."]
theorem polynomialLaurentIso_minus (a : Under R) :
    laurentMinus P a ≫ (polynomialIso P a).hom =
      (laurentIso P a).hom ≫
        (baseProductTransformation _ _ (PolynomialLaurent.laurentMinus
          (CommRingCat.of (ULift.{u} ℤ)))
          (PolynomialLaurent.laurentMinus_projection
          (CommRingCat.of (ULift.{u} ℤ)))).app (space (op P, a)) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, polynomialIso_hom_fst, baseProductTransformation,
      pullback.lift_fst, Category.comp_id, laurentIso_hom_fst, laurentMinus_projection]
  · simp only [Category.assoc, polynomialIso_hom_snd, baseProductTransformation,
      pullback.lift_snd, laurentIso_hom_snd_assoc]
    change coefficientMap P ((underToLaurentInvert R).app a) ≫
      coefficientProjection (op P, (polynomialUnderFunctor R).obj a) ≫ _ = _
    rw [coefficientMap_coefficientProjection_assoc]
    change coefficientProjection (op P, (laurentUnderFunctor R).obj a) ≫
      PolynomialLaurent.laurentMinus a.right ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (integerMap a.right).hom)) = _
    rw [PolynomialLaurent.laurentMinus, PolynomialLaurent.laurentMinus,
      ← Spec.map_comp, ← Spec.map_comp, inverseChart_naturality]

/-- The common integer-coordinate unit pulls back to the original native forward unit. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/BaseChange/Coefficients/PolynomialLaurent.lean:213"
  "adaptation" "Actual coefficient product projections, oriented charts and original naturality."]
theorem laurentIso_globalUnit (a : Under R) :
    Units.map (laurentIso P a).hom.appTop.hom.toMonoidHom
      (Units.map (pullback.snd (specULiftZIsTerminal.from (space (op P, a)))
        (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u} ℤ)))).appTop.hom.toMonoidHom
          (PolynomialLaurent.laurentCoordinate (CommRingCat.of (ULift.{u} ℤ)))) =
      Units.map (coefficientProjection (op P, (laurentUnderFunctor R).obj a)).appTop.hom.toMonoidHom
        (PolynomialLaurent.laurentCoordinate a.right) := by
  have hu := PolynomialLaurent.laurentCoordinate_coefficient (integerMap a.right)
  rw [← hu]
  apply Units.ext
  have h := congrArg (fun g => g.appTop) (laurentIso_hom_snd P a)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h
    (↑(PolynomialLaurent.laurentCoordinate
          (CommRingCat.of (ULift.{u} ℤ))))

end AlgebraicGeometry.Scheme.BaseChange.Coefficients
