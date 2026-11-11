module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedParameterCoefficientModels
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
noncomputable section
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]
example : (parameterSupportedRowIso f).hom ≫ supportedRowForget f =
    Functor.whiskerLeft specUnder (ParameterModels.forget f.left) ≫
      (parameterRowModelIso Q).hom := parameterSupportedRowIso_forget f
example : (parameterSupportedRowIso f).hom ≫ supportedRowRestriction f ≫
    AlgebraicGeometry.Scheme.Modules.boundedAboveFlatCoefficientSupportedForgetModelTransformation f
      =
      Functor.whiskerLeft specUnder (ParameterModels.forget f.left) ≫
        parameterCoefficientRestriction Q := parameterSupportedRowIso_restriction_forget f
