module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedRestrictionModel
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : CommRingCat.{u}) (c : Index R) {U : Scheme.{u}}
    (j : U ⟶ space c) [IsOpenImmersion j]
example : (supportedRestriction R c j).IsEquivalence :=
  supportedRestriction_isEquivalence R c j
example {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] (a : Under R) :
    supportedRestrictionModel R (Opposite.op Q, a) (schemeMap f a) ≫
        boundedAboveFlatCoefficientSupportedForgetModelMap f a =
      boundedAboveFlatGlobalSupportedForget
        (X := (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj
          (Opposite.op Q, a)) (schemeMap f a) ≫
        (boundedAboveFlatGlobalCoefficientModelRestriction R).app (Opposite.op Q, a) :=
  supportedRestrictionModel_forget R f a
end
