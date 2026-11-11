module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenKZeroExact

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry
open CategoryTheory.Waldhausen.AlgebraicGrothendieck
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

example [CompactSpace P.left] (a : Under R) :
    Function.Surjective
      (KMap (Fibration.changeWeak_exact
        (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).nested) 0) :=
  boundedAboveFlatCoefficientSupportedOpenGrading_KMap_zero_surjective f T a

example [CompactSpace P.left] [CompactSpace Q.left] (a : Under R) :
    (KMap (boundedAboveFlatCoefficientSupportedOpenRestriction_exact f T a) 0).range =
      (KMap (Fibration.changeWeak_exact
        (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).nested) 0).ker :=
  boundedAboveFlatCoefficientSupportedOpenGrading_KMap_zero_range_ker f T a

example [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]
    [CompactSpace T] (a : Under R) :
    Function.Injective
      (KMap (boundedAboveFlatCoefficientSupportedOpenRestrictionModelMap f T a).hom.isExact 0) ∧
      (KMap (boundedAboveFlatCoefficientSupportedOpenRestrictionModelMap f T a).hom.isExact
        0).range =
        (KMap (boundedAboveFlatCoefficientSupportedOpenGradingModelMap f T a).hom.isExact 0).ker ∧
      Function.Surjective
        (KMap (boundedAboveFlatCoefficientSupportedOpenGradingModelMap f T a).hom.isExact 0) :=
  boundedAboveFlatCoefficientSupportedOpenModel_KZero_exact f T a

example [CompactSpace P.left]
    (a : Under R) :
    (grothendieckKZeroEquivOfAsSmall
      (perfectSupportedWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)).symm.toMonoidHom.comp
        (boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv f T a 0).toMonoidHom =
      (AlgebraicGrothendieck.map (boundedAboveFlatCoefficientSupportedSectionWaldhausen
        (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)
        (boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation f T a)
        (boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation_exact
          f T a)).toMultiplicative.comp
          (grothendieckKZeroEquivOfAsSmall
            (boundedAboveFlatCoefficientSupportedSectionWaldhausen
              (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)).symm.toMonoidHom :=
  boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv_grothendieck f T a

example [CompactSpace P.left]
    (a : Under R) :
    (boundedAboveFlatCoefficientSupportedOpenKZeroValueMap f T a).comp
        (KMap (Fibration.changeWeak_exact
          (boundedAboveFlatCoefficientSupportedFullOpenGrading f T a).nested) 0) =
      (QuotientAddGroup.mk'
        (AlgebraicGrothendieck.map (perfectSupportedOpenWeakWaldhausen (schemeMap f a)
          (boundedAboveFlatCoefficientSupportOpen Q T a))
          (perfectSupportedRestrict (schemeMap f a) (boundedAboveFlatCoefficientSupportOpen Q T a))
          (perfectSupportedOpenRestrict_waldhausenExact (schemeMap f a)
            (boundedAboveFlatCoefficientSupportOpen Q T a))).range).toMultiplicative.comp
        ((grothendieckKZeroEquivOfAsSmall
          (perfectSupportedWaldhausen
            (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι)).symm.toMonoidHom.comp
            (boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv f T a 0).toMonoidHom) :=
  boundedAboveFlatCoefficientSupportedOpenKZeroValueMap_comp_grading f T a
