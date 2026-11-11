module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedCoefficientRestriction
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : CommRingCat.{u}) (c : Index R) {U : Scheme.{u}}
    (j : U ⟶ space c) [IsOpenImmersion j]
example : supportedRestriction R c j ⋙ (boundedAboveFlatCoefficientSectionSupported j).ι =
    (boundedAboveFlatGlobalSectionSupported
      (X := (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j).ι ⋙
        ((boundedAboveFlatGlobalCoefficientModelRestriction R).app c).hom.toFunctor :=
  supportedRestriction_forget R c j
example : supportedRestriction R c j ⋙ boundedAboveFlatCoefficientSupportedEvaluation j =
    boundedAboveFlatGlobalSupportedEvaluation
      (X := (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j :=
  supportedRestriction_evaluation R c j
end
