/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.AlgebraicGeometry.Scheme.CoefficientPolynomialLaurentSchemeNaturality
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientOpenRestriction
public import Colib.AlgebraicGeometry.Scheme.QuasiCompactOpenPairPolynomialLaurent
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientPolynomialLaurentTransport

/-!
Source in `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/`:
`CoefficientSupportedPolynomialLaurentTransport.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Original polynomial and Laurent transport for native coefficient open pairs

An open immersion over the fixed base defines a functor of actual open pairs on
all coefficient algebras. The original native polynomial and Laurent product
isomorphisms lift to these pairs, preserving both chart maps. This supplies the
actual two-chart contraction transport, including its original Laurent quotient.
Only compactness of the ambient scheme is needed for this geometric interface.
The subsequent supported finite-bottom comparison has separate K-zero input.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent
universe u w
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- The unchanged native open pairs and all original coefficient squares, with qc ambient. -/
def boundedAboveFlatCoefficientQuasiCompactOpenPairRow : Under R ⥤ QuasiCompactOpenPairs.{u}ᵒᵖ where
  obj a := op ⟨boundedAboveFlatCoefficientOpenPair f a, compactSpace_space (op Q, a)⟩
  map g := (ObjectProperty.homMk (boundedAboveFlatCoefficientOpenPairMap f g)).op
  map_id a := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Arrow.Hom.ext
    · exact AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_id (op P, a)
    · exact AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_id (op Q, a)
  map_comp {a b c} g h := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Arrow.Hom.ext
    · exact coefficientMap_comp P g h
    · exact coefficientMap_comp Q g h

/-- Forgetting the removed open gives exactly the original compact ambient coefficient row. -/
theorem boundedAboveFlatCoefficientQuasiCompactOpenPairRow_base :
    boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ quasiCompactOpenPairsBase.op =
      boundedAboveFlatCoefficientQuasiCompactRow Q := rfl

/-- The original polynomial product comparison as an isomorphism of actual open pairs. -/
def boundedAboveFlatCoefficientOpenPairPolynomialIso (a : Under R) :
    ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj
      ((polynomialUnderFunctor R).obj a)).unop ≅
      Scheme.Bass.pairPolynomialFunctor.obj
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a).unop :=
  quasiCompactOpenPairProperty.isoMk
    (MorphismProperty.Arrow.isoMk (polynomialIso P a) (polynomialIso Q a)
      (polynomialIso_schemeMap f a).symm)

/-- The same actual polynomial pair isomorphisms are natural in every coefficient arrow. -/
def boundedAboveFlatCoefficientSupportedPolynomialIso :
    polynomialUnderFunctor R ⋙ boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ≅
      boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ Scheme.Bass.pairPolynomialFunctor.op :=
  NatIso.ofComponents (fun a ↦ (boundedAboveFlatCoefficientOpenPairPolynomialIso f a).symm.op) (by
    intro a b g
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Arrow.Hom.ext
    · change (polynomialIso P b).inv ≫
        coefficientMap P ((polynomialUnderFunctor R).map g) =
          (Scheme.Products.baseProductFunctor
            (PolynomialLaurent.polynomialProjection
              (CommRingCat.of (ULift.{u} ℤ)))).map (coefficientMap P g) ≫
                (polynomialIso P a).inv
      apply (cancel_mono (polynomialIso P a).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [polynomialIso_naturality P g, Iso.inv_hom_id_assoc]
    · change (polynomialIso Q b).inv ≫
        coefficientMap Q ((polynomialUnderFunctor R).map g) =
          (Scheme.Products.baseProductFunctor
            (PolynomialLaurent.polynomialProjection
              (CommRingCat.of (ULift.{u} ℤ)))).map (coefficientMap Q g) ≫
                (polynomialIso Q a).inv
      apply (cancel_mono (polynomialIso Q a).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [polynomialIso_naturality Q g, Iso.inv_hom_id_assoc])

/-- The original laurent product comparison as an isomorphism of actual open pairs. -/
def boundedAboveFlatCoefficientOpenPairLaurentIso (a : Under R) :
    ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj
      ((laurentUnderFunctor R).obj a)).unop ≅
      Scheme.Bass.pairLaurentFunctor.obj
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a).unop :=
  quasiCompactOpenPairProperty.isoMk
    (MorphismProperty.Arrow.isoMk (laurentIso P a) (laurentIso Q a) (laurentIso_schemeMap f a).symm)

/-- The same actual laurent pair isomorphisms are natural in every coefficient arrow. -/
def boundedAboveFlatCoefficientSupportedLaurentIso :
    laurentUnderFunctor R ⋙ boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ≅
      boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ Scheme.Bass.pairLaurentFunctor.op :=
  NatIso.ofComponents (fun a ↦ (boundedAboveFlatCoefficientOpenPairLaurentIso f a).symm.op) (by
    intro a b g
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Arrow.Hom.ext
    · change (laurentIso P b).inv ≫
        coefficientMap P ((laurentUnderFunctor R).map g) =
          (Scheme.Products.baseProductFunctor
            (PolynomialLaurent.laurentProjection
              (CommRingCat.of (ULift.{u} ℤ)))).map (coefficientMap P g) ≫
                (laurentIso P a).inv
      apply (cancel_mono (laurentIso P a).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [laurentIso_naturality P g, Iso.inv_hom_id_assoc]
    · change (laurentIso Q b).inv ≫
        coefficientMap Q ((laurentUnderFunctor R).map g) =
          (Scheme.Products.baseProductFunctor
            (PolynomialLaurent.laurentProjection
              (CommRingCat.of (ULift.{u} ℤ)))).map (coefficientMap Q g) ≫
                (laurentIso Q a).inv
      apply (cancel_mono (laurentIso Q a).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [laurentIso_naturality Q g, Iso.inv_hom_id_assoc])

/-- The actual supported plus chart square, before applying any K-theory functor. -/
@[reassoc] theorem boundedAboveFlatCoefficientSupportedPolynomialLaurentIso_plus (a : Under R) :
    (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).map ((underToLaurent R).app a) ≫
        (boundedAboveFlatCoefficientSupportedLaurentIso f).hom.app a =
      (boundedAboveFlatCoefficientSupportedPolynomialIso f).hom.app a ≫
        (NatTrans.op Scheme.Bass.pairPlus).app
          ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply MorphismProperty.Arrow.Hom.ext
  · change (laurentIso P a).inv ≫ laurentPlus P a =
      (Scheme.Products.baseProductTransformation _ _
        (PolynomialLaurent.laurentToPolynomial (CommRingCat.of (ULift.{u} ℤ)))
        (PolynomialLaurent.laurentToPolynomial_projection
          (CommRingCat.of (ULift.{u} ℤ)))).app (space (op P, a)) ≫
            (polynomialIso P a).inv
    apply (cancel_mono (polynomialIso P a).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [polynomialLaurentIso_plus P a, Iso.inv_hom_id_assoc]
  · change (laurentIso Q a).inv ≫ laurentPlus Q a =
      (Scheme.Products.baseProductTransformation _ _
        (PolynomialLaurent.laurentToPolynomial (CommRingCat.of (ULift.{u} ℤ)))
        (PolynomialLaurent.laurentToPolynomial_projection
          (CommRingCat.of (ULift.{u} ℤ)))).app (space (op Q, a)) ≫
            (polynomialIso Q a).inv
    apply (cancel_mono (polynomialIso Q a).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [polynomialLaurentIso_plus Q a, Iso.inv_hom_id_assoc]

/-- The actual supported minus chart square, before applying any K-theory functor. -/
@[reassoc] theorem boundedAboveFlatCoefficientSupportedPolynomialLaurentIso_minus (a : Under R) :
    (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).map ((underToLaurentInvert R).app a) ≫
        (boundedAboveFlatCoefficientSupportedLaurentIso f).hom.app a =
      (boundedAboveFlatCoefficientSupportedPolynomialIso f).hom.app a ≫
        (NatTrans.op Scheme.Bass.pairMinus).app
          ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply MorphismProperty.Arrow.Hom.ext
  · change (laurentIso P a).inv ≫ laurentMinus P a =
      (Scheme.Products.baseProductTransformation _ _
        (PolynomialLaurent.laurentMinus (CommRingCat.of (ULift.{u} ℤ)))
        (PolynomialLaurent.laurentMinus_projection
          (CommRingCat.of (ULift.{u} ℤ)))).app (space (op P, a)) ≫
            (polynomialIso P a).inv
    apply (cancel_mono (polynomialIso P a).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [polynomialLaurentIso_minus P a, Iso.inv_hom_id_assoc]
  · change (laurentIso Q a).inv ≫ laurentMinus Q a =
      (Scheme.Products.baseProductTransformation _ _
        (PolynomialLaurent.laurentMinus (CommRingCat.of (ULift.{u} ℤ)))
        (PolynomialLaurent.laurentMinus_projection
          (CommRingCat.of (ULift.{u} ℤ)))).app (space (op Q, a)) ≫
            (polynomialIso Q a).inv
    apply (cancel_mono (polynomialIso Q a).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [polynomialLaurentIso_minus Q a, Iso.inv_hom_id_assoc]

/-- Genuine original two-chart cokernel transport on the existing native coefficient row. -/
def boundedAboveFlatCoefficientSupportedContractionTransportIso
    (F : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    KTheory.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
        (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ F) ≅
      boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙
        KTheory.Bass.TwoChart.contraction (NatTrans.op
          Scheme.Bass.pairPlus)
          (NatTrans.op Scheme.Bass.pairMinus) F :=
  KTheory.Bass.TwoChart.contractionTransportIso
    (NatTrans.op Scheme.Bass.pairPlus) (NatTrans.op
      Scheme.Bass.pairMinus)
    (underToLaurent R) (underToLaurentInvert R)
    (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f)
    (boundedAboveFlatCoefficientSupportedPolynomialIso f)
    (boundedAboveFlatCoefficientSupportedLaurentIso f)
    (boundedAboveFlatCoefficientSupportedPolynomialLaurentIso_plus f)
    (boundedAboveFlatCoefficientSupportedPolynomialLaurentIso_minus f) F

/-- The same transport retains the original native Laurent quotient representative. -/
@[reassoc] theorem boundedAboveFlatCoefficientSupportedContractionTransportIso_π
    (F : AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) (a : Under R) :
    (KTheory.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
      (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ F)).app a ≫
        (boundedAboveFlatCoefficientSupportedContractionTransportIso f F).hom.app a =
      F.map ((boundedAboveFlatCoefficientSupportedLaurentIso f).hom.app a) ≫
        (KTheory.Bass.TwoChart.contractionπ (NatTrans.op
          Scheme.Bass.pairPlus)
          (NatTrans.op Scheme.Bass.pairMinus) F).app
            ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) :=
  KTheory.Bass.TwoChart.contractionTransportIso_π
    (NatTrans.op Scheme.Bass.pairPlus) (NatTrans.op
      Scheme.Bass.pairMinus)
    (underToLaurent R) (underToLaurentInvert R)
    (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f)
    (boundedAboveFlatCoefficientSupportedPolynomialIso f)
    (boundedAboveFlatCoefficientSupportedLaurentIso f)
    (boundedAboveFlatCoefficientSupportedPolynomialLaurentIso_plus f)
    (boundedAboveFlatCoefficientSupportedPolynomialLaurentIso_minus f) F a


attribute [colib_ref "quillen" "CoefficientSupportedPolynomialLaurentTransport.lean:37"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientQuasiCompactOpenPairRow
attribute [colib_ref "quillen" "CoefficientSupportedPolynomialLaurentTransport.lean:56"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientQuasiCompactOpenPairRow_base
attribute [colib_ref "quillen" "CoefficientSupportedPolynomialLaurentTransport.lean:61"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientOpenPairPolynomialIso
attribute [colib_ref "quillen" "CoefficientSupportedPolynomialLaurentTransport.lean:70"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedPolynomialIso
attribute [colib_ref "quillen" "CoefficientSupportedPolynomialLaurentTransport.lean:99"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientOpenPairLaurentIso
attribute [colib_ref "quillen" "CoefficientSupportedPolynomialLaurentTransport.lean:108"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedLaurentIso
attribute [colib_ref "quillen" "CoefficientSupportedPolynomialLaurentTransport.lean:137"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedPolynomialLaurentIso_plus
attribute [colib_ref "quillen" "CoefficientSupportedPolynomialLaurentTransport.lean:167"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedPolynomialLaurentIso_minus
attribute [colib_ref "quillen" "CoefficientSupportedPolynomialLaurentTransport.lean:197"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedContractionTransportIso
attribute [colib_ref "quillen" "CoefficientSupportedPolynomialLaurentTransport.lean:215"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedContractionTransportIso_π

end AlgebraicGeometry.Scheme.Modules
