module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenKZeroExact

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Waldhausen
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.AlgebraicGrothendieck
universe u
variable {R : CommRingCat.{u}}

variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

omit [IsOpenImmersion f.left] in
example [CompactSpace P.left]
    (a : Under R) :
    (grothendieckKZeroEquivOfAsSmall
      (RingedSpace.perfectComplexesWaldhausen (space (op P,
        a)).toRingedSpace)).symm.toMonoidHom.comp
        (boundedAboveFlatCoefficientFullOpenPerfectKEquiv f a 0).toMonoidHom =
      (AlgebraicGrothendieck.map (boundedAboveFlatCoefficientSectionWaldhausen (op P, a))
        (boundedAboveFlatCoefficientFullOpenPerfectEvaluation f a)
        (boundedAboveFlatCoefficientFullOpenPerfectEvaluation_exact f a)).toMultiplicative.comp
          (grothendieckKZeroEquivOfAsSmall
            (boundedAboveFlatCoefficientSectionWaldhausen (op P, a))).symm.toMonoidHom :=
  boundedAboveFlatCoefficientFullOpenPerfectKEquiv_grothendieck f a

example [CompactSpace P.left]
    (a : Under R) :
    (boundedAboveFlatCoefficientOpenKZeroValueMap f a).comp
        (KMap (Fibration.changeWeak_exact (boundedAboveFlatCoefficientFullOpenGrading f a).nested)
          0) =
      (QuotientAddGroup.mk'
        (AlgebraicGrothendieck.map (perfectOpenWeakWaldhausen (schemeMap f a))
          (perfectComplexesRestrictOpenImmersion (schemeMap f a))
          (perfectOpenRestrict_isExact (schemeMap f a))).range).toMultiplicative.comp
        ((grothendieckKZeroEquivOfAsSmall
          (RingedSpace.perfectComplexesWaldhausen (space (op P,
            a)).toRingedSpace)).symm.toMonoidHom.comp
            (boundedAboveFlatCoefficientFullOpenPerfectKEquiv f a 0).toMonoidHom) :=
  boundedAboveFlatCoefficientOpenKZeroValueMap_comp_grading f a

example [CompactSpace P.left]
    (a : Under R) :
    Function.Surjective
      (KMap (Fibration.changeWeak_exact (boundedAboveFlatCoefficientFullOpenGrading f a).nested)
        0) :=
  boundedAboveFlatCoefficientOpenGrading_KMap_zero_surjective f a

example
    [CompactSpace P.left] [CompactSpace Q.left] (a : Under R) :
    (KMap (boundedAboveFlatCoefficientOpenRestriction_exact f a) 0).range =
      (KMap (Fibration.changeWeak_exact
        (boundedAboveFlatCoefficientFullOpenGrading f a).nested) 0).ker :=
  boundedAboveFlatCoefficientOpenGrading_KMap_zero_range_ker f a

example [CompactSpace P.left]
    [CompactSpace Q.left] [QuasiSeparatedSpace Q.left] (a : Under R) :
    Function.Injective (KMap (boundedAboveFlatCoefficientOpenRestrictionModelMap f a).hom.isExact
      0) ∧
      (KMap (boundedAboveFlatCoefficientOpenRestrictionModelMap f a).hom.isExact 0).range =
        (KMap (boundedAboveFlatCoefficientOpenGradingModelMap f a).hom.isExact 0).ker ∧
      Function.Surjective (KMap (boundedAboveFlatCoefficientOpenGradingModelMap f a).hom.isExact
        0) :=
  boundedAboveFlatCoefficientOpenModel_KZero_exact f a

