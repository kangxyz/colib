module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalOpenModels
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
example : openRowChangeWeak f ≫ openRowRestriction f =
    rowRestriction Q ≫ boundedAboveFlatCoefficientOpenChangeWeakModelTransformation f :=
  openRowRestriction_changeWeak f
example (a : Under R) : openChangeWeak f a ≫ openRestriction f a =
    (rowRestriction Q).app a ≫ boundedAboveFlatCoefficientOpenChangeWeakModelMap f a :=
  openRestriction_changeWeak f a
end
