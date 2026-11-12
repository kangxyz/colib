module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedRow
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
universe u
noncomputable section
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]
example :
    supportedRowRestriction f ≫ boundedAboveFlatCoefficientSupportedForgetModelTransformation f =
    supportedRowForget f ≫ rowRestriction Q := supportedRowRestriction_forget f
example {a b : Under R} (g : a ⟶ b) :
    supportedRowMapFunctor f g ⋙ supportedRestriction R (Opposite.op Q, b)
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.schemeMap f b) =
      supportedRestriction R (Opposite.op Q, a)
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.schemeMap f a) ⋙
        (boundedAboveFlatCoefficientSupportedModelMap f g).hom.toFunctor :=
  supportedRowMap_restriction f g
end
