module
import Colib.AlgebraicGeometry.Scheme.GlobalAuxiliaryCoefficientPairs

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
noncomputable section
universe u

section General
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left] (T : Q.left.Opens) (a : Under R)

example : boundedAboveFlatCoefficientFiberSupportOpen f T a =
    projection (op Q, a) ⁻¹ᵁ (T ⊔ f.left.opensRange) := fiberSupportOpen_eq f T a

example : supportObject Q T ⟶ Q := supportArrow Q T

example : IsOpenImmersion (supportArrow Q T).left := inferInstance

example : (schemeMap (supportArrow Q T) a).opensRange =
    boundedAboveFlatCoefficientSupportOpen Q T a := supportArrow_range Q T a

example : ((boundedAboveFlatCoefficientSupportOpen Q T a) : Scheme.{u}) ≅
    space (op (supportObject Q T), a) := supportRangeIso Q T a

example : (supportRangeIso Q T a).hom ≫ schemeMap (supportArrow Q T) a =
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι := supportRangeIso_fac Q T a

example : Scheme.supportOpenPair (boundedAboveFlatCoefficientSupportOpen Q T a) ≅
    boundedAboveFlatCoefficientOpenPair (supportArrow Q T) a := supportPairIso Q T a

example : (supportPairIso Q T a).hom.right = 𝟙 _ := supportPairIso_hom_right Q T a
end General

section Integral
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) (T : Q.left.Opens) (a : Under (CommRingCat.of (ULift.{u} ℤ)))

example : (canonicalRowIso Q a).hom ⁻¹ᵁ
      (CategoryTheory.Limits.pullback.snd (specULiftZIsTerminal.from (Spec a.right))
        (specULiftZIsTerminal.from Q.left) ⁻¹ᵁ T) =
    boundedAboveFlatCoefficientSupportOpen Q T a := row_supportOpen Q T a

example [IsOpenImmersion f.left] : (canonicalRowIso Q a).hom ⁻¹ᵁ
      (CategoryTheory.Limits.pullback.snd (specULiftZIsTerminal.from (Spec a.right))
        (specULiftZIsTerminal.from Q.left) ⁻¹ᵁ (T ⊔ f.left.opensRange)) =
    boundedAboveFlatCoefficientFiberSupportOpen f T a := row_fiberSupportOpen f T a

example : (canonicalRowIso P a).hom ⁻¹ᵁ
      (CategoryTheory.Limits.pullback.snd (specULiftZIsTerminal.from (Spec a.right))
        (specULiftZIsTerminal.from P.left) ⁻¹ᵁ (f.left ⁻¹ᵁ T)) =
    boundedAboveFlatCoefficientOpenSupportOpen f T a := row_openSupportOpen f T a

example : Scheme.supportOpenPair (boundedAboveFlatCoefficientSupportOpen Q T a) ≅
    Scheme.GlobalSupportedParameter.pair T.ι (Spec a.right) := parameterSupportPairIso Q T a

example : (parameterSupportPairIso Q T a).hom.right = (canonicalRowIso Q a).hom :=
  parameterSupportPairIso_hom_right Q T a
end Integral
