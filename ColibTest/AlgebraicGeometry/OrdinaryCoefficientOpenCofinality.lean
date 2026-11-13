module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenCofinality
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Waldhausen
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (a : Under R) (n : ℕ)
example (x : (boundedAboveFlatCoefficientOpenWaldhausen f a).K n) :
    boundedAboveFlatCoefficientSectionKEquiv (op P, a) n
        (KMap (boundedAboveFlatCoefficientOpenRestriction_exact f a) n x) =
      boundedAboveFlatPerfectOpenKRestrict (schemeMap f a) n
        (boundedAboveFlatCoefficientOpenKEquiv f a n x) :=
  boundedAboveFlatCoefficientOpenRestriction_KComparison f a n x
variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]
example : Function.Injective (KMap (boundedAboveFlatCoefficientOpenRestriction_exact f a) 0) :=
  boundedAboveFlatCoefficientOpenRestriction_KMap_zero_injective f a
example :
    Function.Bijective (KMap (boundedAboveFlatCoefficientOpenRestriction_exact f a) (n + 1)) :=
  boundedAboveFlatCoefficientOpenRestriction_KMap_succ_bijective f a n
