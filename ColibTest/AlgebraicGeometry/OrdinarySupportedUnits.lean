module
import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientOrdinarySupportedUnits
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Functor.IdentityAutomorphism CommRingCat.PolynomialLaurent
universe u
noncomputable section
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]
example {a b : Under R} (g : a ⟶ b) :
    Preserves ((boundedAboveFlatCoefficientSupportedModelFunctor f).map
      ((laurentUnderFunctor R).map g)).hom.toFunctor
      (boundedAboveFlatCoefficientSupportedLaurentUnitIso f a)
      (boundedAboveFlatCoefficientSupportedLaurentUnitIso f b) :=
  boundedAboveFlatCoefficientSupportedLaurentUnitIso_coefficient f g
example (a : Under R) :
    𝟭 (boundedAboveFlatCoefficientSectionSupported
      (schemeMap f ((laurentUnderFunctor R).obj a))).FullSubcategory ≅
      𝟭 (boundedAboveFlatCoefficientSectionSupported
        (schemeMap f ((laurentUnderFunctor R).obj a))).FullSubcategory :=
  boundedAboveFlatCoefficientSupportedLaurentUnitIso f a
end
