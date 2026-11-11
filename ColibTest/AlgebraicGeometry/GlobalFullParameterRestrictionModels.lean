module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientRestriction
@[expose] public noncomputable section
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
section
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
example : globalOpenRestriction f ≫ rowRestriction P =
    openRowRestriction f ≫ boundedAboveFlatCoefficientOpenRestrictionModelTransformation f :=
  globalOpenRestriction_square f
end
section
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
  (f : P ⟶ Q) [IsOpenImmersion f.left]
example : Functor.whiskerLeft specUnder (parameterFullRestriction f) ≫
    (parameterRowModelIso P).hom =
      (parameterRowModelIso Q).hom ≫ globalOpenFineRestriction f :=
  fullRestriction_model_square f
end
