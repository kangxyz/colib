module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterCoefficientModels

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
noncomputable section
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterAuxiliarySupport.ambient T).obj (specUnder.obj a) ⟶
      boundedAboveFlatCoefficientSupportedAmbientModel T a := ambientComponent Q T a

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterAuxiliarySupport.fiber f.left T).obj (specUnder.obj a) ⟶
      boundedAboveFlatCoefficientSupportedFiberModel f T a := fiberComponent f T a

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterAuxiliarySupport.openModel f.left T).obj (specUnder.obj a) ⟶
      boundedAboveFlatCoefficientSupportedFullOpenModel f T a := openComponent f T a

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ambientComponent Q T a).hom.toFunctor.obj
        ((ParameterAuxiliarySupport.ambient T).obj (specUnder.obj a)).obj.waldhausen.zero =
      (boundedAboveFlatCoefficientSupportedAmbientModel T a).obj.waldhausen.zero :=
  ambientComponent_zero Q T a

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    boundedAboveFlatCoefficientSupportedAmbientModel (T ⊔ f.left.opensRange) a =
      boundedAboveFlatCoefficientSupportedFiberModel f T a :=
  fiberModel_eq f T a

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    boundedAboveFlatCoefficientSupportedAmbientModel (f.left ⁻¹ᵁ T) a =
      boundedAboveFlatCoefficientSupportedFullOpenModel f T a :=
  openModel_eq f T a

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (fiberComponent f T a).hom.toFunctor.obj
        ((ParameterAuxiliarySupport.fiber f.left T).obj (specUnder.obj a)).obj.waldhausen.zero =
      (boundedAboveFlatCoefficientSupportedFiberModel f T a).obj.waldhausen.zero :=
  fiberComponent_zero f T a

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (openComponent f T a).hom.toFunctor.obj
        ((ParameterAuxiliarySupport.openModel f.left T).obj (specUnder.obj a)).obj.waldhausen.zero =
      (boundedAboveFlatCoefficientSupportedFullOpenModel f T a).obj.waldhausen.zero :=
  openComponent_zero f T a

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    fiberComponent f T a =
      ambientComponent Q (T ⊔ f.left.opensRange) a ≫ eqToHom (fiberModel_eq f T a) := rfl
