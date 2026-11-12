module
import Colib.AlgebraicGeometry.Scheme.GlobalSupportedCoefficientGeometry
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.GlobalSupportedParameter
universe u
noncomputable section
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]
example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (coefficientPairIso f a).hom.left = (canonicalRowIso P a).hom :=
  coefficientPairIso_hom_left f a
example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (coefficientPairIso f a).hom.right = (canonicalRowIso Q a).hom :=
  coefficientPairIso_hom_right f a
