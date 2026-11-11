/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.Polynomial.LaurentBaseChange
public import Colib.AlgebraicGeometry.Scheme.IntegerBaseProducts
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentProjection
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # The actual affine polynomial and Laurent product comparisons

The original ring pushouts give the genuine affine-to-product pullback isomorphisms.
Both projections, every coefficient morphism, and both oriented chart squares are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
universe u
namespace AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

/-- The actual initial integral coefficient map. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/BaseChange.lean:37"
  "adaptation" "Original affine pullback comparison with both projections and oriented charts"]
def integerMap (R : CommRingCat.{u}) : (CommRingCat.of (ULift.{u} ℤ)) ⟶ R :=
  CommRingCat.isInitial.to R

/-- The spectrum of the original integral structure map is the terminal projection. -/
@[simp, colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/BaseChange.lean:39"
  "adaptation" "Original affine pullback comparison with both projections and oriented charts"]
lemma spec_integerMap (R : CommRingCat.{u}) :
    Spec.map (integerMap R) = specULiftZIsTerminal.from (Spec R) := specULiftZIsTerminal.hom_ext _ _

/-- The direct affine polynomial model gives the genuine base-product pullback square. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/BaseChange.lean:43"
  "adaptation" "Original affine pullback comparison with both projections and oriented charts"]
lemma polynomialSpec_isPullback (R : CommRingCat.{u}) :
    IsPullback (PolynomialLaurent.polynomialProjection R)
      (Spec.map ((CommRingCat.ofHom (Polynomial.mapRingHom (integerMap R).hom))))
      (specULiftZIsTerminal.from (Spec R)) (PolynomialLaurent.polynomialProjection (CommRingCat.of
        (ULift.{u}
        ℤ))) := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.PolynomialLaurent.polynomial_isPushout (integerMap R))
  simpa only [spec_integerMap,
    PolynomialLaurent.polynomialProjection] using h

/-- The direct affine Laurent model gives the genuine base-product pullback square. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/BaseChange.lean:53"
  "adaptation" "Original affine pullback comparison with both projections and oriented charts"]
lemma laurentSpec_isPullback (R : CommRingCat.{u}) :
    IsPullback (PolynomialLaurent.laurentProjection R)
      (Spec.map ((CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ (integerMap R).hom))))
      (specULiftZIsTerminal.from (Spec R)) (PolynomialLaurent.laurentProjection (CommRingCat.of
        (ULift.{u}
        ℤ))) := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.PolynomialLaurent.laurent_isPushout (integerMap R))
  simpa only [spec_integerMap, PolynomialLaurent.laurentCoefficientInclusion,
    PolynomialLaurent.laurentProjection] using h

/-- The actual polynomial affine-to-product isomorphism. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/BaseChange.lean:63"
  "adaptation" "Original affine pullback comparison with both projections and oriented charts"]
def polynomialSpecIso (R : CommRingCat.{u}) :
    Spec (.of (Polynomial R)) ≅
      (baseProductFunctor (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u}
        ℤ)))).obj (Spec R) :=
  (polynomialSpec_isPullback R).isoPullback

/-- The actual Laurent affine-to-product isomorphism. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/BaseChange.lean:69"
  "adaptation" "Original affine pullback comparison with both projections and oriented charts"]
def laurentSpecIso (R : CommRingCat.{u}) :
    Spec (.of (LaurentPolynomial R)) ≅
      (baseProductFunctor (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u}
        ℤ)))).obj (Spec R) :=
  (laurentSpec_isPullback R).isoPullback

/-- The first affine-product projection is the original polynomial coefficient projection. -/
@[reassoc (attr := simp),
  colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/BaseChange.lean:74"
  "adaptation" "Original affine pullback comparison with both projections and oriented charts"]
lemma polynomialSpecIso_hom_fst (R : CommRingCat.{u}) :
    (polynomialSpecIso R).hom ≫ pullback.fst _ _ = PolynomialLaurent.polynomialProjection R :=
  (polynomialSpec_isPullback R).isoPullback_hom_fst

/-- The second affine-product projection is the original integral polynomial map. -/
@[reassoc (attr := simp),
  colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/BaseChange.lean:78"
  "adaptation" "Original affine pullback comparison with both projections and oriented charts"]
lemma polynomialSpecIso_hom_snd (R : CommRingCat.{u}) :
    (polynomialSpecIso R).hom ≫ pullback.snd _ _ =
      Spec.map ((CommRingCat.ofHom (Polynomial.mapRingHom (integerMap R).hom))) :=
  (polynomialSpec_isPullback R).isoPullback_hom_snd

/-- The first affine-product projection is the original Laurent coefficient projection. -/
@[reassoc (attr := simp),
  colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/BaseChange.lean:83"
  "adaptation" "Original affine pullback comparison with both projections and oriented charts"]
lemma laurentSpecIso_hom_fst (R : CommRingCat.{u}) :
    (laurentSpecIso R).hom ≫ pullback.fst _ _ = PolynomialLaurent.laurentProjection R :=
  (laurentSpec_isPullback R).isoPullback_hom_fst

/-- The second affine-product projection is the original integral Laurent map. -/
@[reassoc (attr := simp),
  colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/BaseChange.lean:87"
  "adaptation" "Original affine pullback comparison with both projections and oriented charts"]
lemma laurentSpecIso_hom_snd (R : CommRingCat.{u}) :
    (laurentSpecIso R).hom ≫ pullback.snd _ _ =
      Spec.map ((CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ (integerMap R).hom))) :=
  (laurentSpec_isPullback R).isoPullback_hom_snd

/-- The unique original integral structure maps commute with every ring morphism. -/
@[simp, reassoc,
  colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/BaseChange.lean:92"
  "adaptation" "Original affine pullback comparison with both projections and oriented charts"]
lemma integerMap_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    integerMap R ≫ f = integerMap S := CommRingCat.isInitial.hom_ext _ _

/-- Naturality of the original polynomial product isomorphism on every ring map. -/
@[reassoc, colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/BaseChange.lean:96"
  "adaptation" "Original affine pullback comparison with both projections and oriented charts"]
lemma polynomialSpecIso_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Spec.map ((CommRingCat.ofHom (Polynomial.mapRingHom f.hom))) ≫ (polynomialSpecIso R).hom =
      (polynomialSpecIso S).hom ≫
        (baseProductFunctor (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u}
          ℤ)))).map (Spec.map f)
          := by
  apply pullback.hom_ext
  · simp only [Category.assoc, polynomialSpecIso_hom_fst, baseProductFunctor,
      pullback.lift_fst, polynomialSpecIso_hom_fst_assoc]
    rw [PolynomialLaurent.polynomialProjection, PolynomialLaurent.polynomialProjection, ←
      Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.PolynomialLaurent.polynomial_coefficient_square f).symm
  · simp only [Category.assoc, polynomialSpecIso_hom_snd, baseProductFunctor,
      pullback.lift_snd, Category.comp_id, ← Spec.map_comp]
    rw [← CommRingCat.PolynomialLaurent.polynomialMap_comp, integerMap_naturality]

/-- Naturality of the original Laurent product isomorphism on every ring map. -/
@[reassoc, colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/BaseChange.lean:112"
  "adaptation" "Original affine pullback comparison with both projections and oriented charts"]
lemma laurentSpecIso_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Spec.map ((CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f.hom))) ≫ (laurentSpecIso R).hom =
      (laurentSpecIso S).hom ≫
        (baseProductFunctor (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u}
          ℤ)))).map (Spec.map f) :=
          by
  apply pullback.hom_ext
  · simp only [Category.assoc, laurentSpecIso_hom_fst, baseProductFunctor,
      pullback.lift_fst, laurentSpecIso_hom_fst_assoc]
    rw [PolynomialLaurent.laurentProjection, PolynomialLaurent.laurentProjection, ← Spec.map_comp, ←
      Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.PolynomialLaurent.laurent_square f).symm
  · simp only [Category.assoc, laurentSpecIso_hom_snd, baseProductFunctor,
      pullback.lift_snd, Category.comp_id, ← Spec.map_comp]
    rw [← CommRingCat.PolynomialLaurent.laurentMap_comp, integerMap_naturality]

/-- The plus chart is preserved by the original affine/product identifications. -/
@[reassoc, colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/BaseChange.lean:128"
  "adaptation" "Original affine pullback comparison with both projections and oriented charts"]
lemma polynomialLaurentSpecIso_plus (R : CommRingCat.{u}) :
    PolynomialLaurent.laurentToPolynomial R ≫ (polynomialSpecIso R).hom =
      (laurentSpecIso R).hom ≫
        (baseProductTransformation _ _ (PolynomialLaurent.laurentToPolynomial (CommRingCat.of
          (ULift.{u} ℤ)))
          (PolynomialLaurent.laurentToPolynomial_projection (CommRingCat.of (ULift.{u} ℤ)))).app
            (Spec R) := by
  apply pullback.hom_ext
  · simp [baseProductTransformation, PolynomialLaurent.laurentToPolynomial_projection]
  · simp only [Category.assoc, polynomialSpecIso_hom_snd, baseProductTransformation,
      pullback.lift_snd, laurentSpecIso_hom_snd_assoc]
    rw [PolynomialLaurent.laurentToPolynomial, PolynomialLaurent.laurentToPolynomial, ←
      Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.PolynomialLaurent.toLaurent_naturality (integerMap R))

/-- The inverse chart is preserved as well, including its actual Laurent inversion. -/
@[reassoc, colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/BaseChange.lean:141"
  "adaptation" "Original affine pullback comparison with both projections and oriented charts"]
lemma polynomialLaurentSpecIso_minus (R : CommRingCat.{u}) :
    PolynomialLaurent.laurentMinus R ≫ (polynomialSpecIso R).hom =
      (laurentSpecIso R).hom ≫
        (baseProductTransformation _ _ (PolynomialLaurent.laurentMinus (CommRingCat.of (ULift.{u}
          ℤ)))
          (PolynomialLaurent.laurentMinus_projection (CommRingCat.of (ULift.{u} ℤ)))).app (Spec R)
            := by
  apply pullback.hom_ext
  · simp [baseProductTransformation, PolynomialLaurent.laurentMinus_projection]
  · simp only [Category.assoc, polynomialSpecIso_hom_snd, baseProductTransformation,
      pullback.lift_snd, laurentSpecIso_hom_snd_assoc]
    rw [PolynomialLaurent.laurentMinus, PolynomialLaurent.laurentMinus, ← Spec.map_comp, ←
      Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.PolynomialLaurent.inverseChart_naturality (integerMap R))

end AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
