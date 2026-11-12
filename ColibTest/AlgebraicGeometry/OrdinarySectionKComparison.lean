module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinarySectionKComparison
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Waldhausen
open AlgebraicGeometry.Scheme.BaseChange.Coefficients AlgebraicGeometry.Scheme.Modules
universe u
variable {R : CommRingCat.{u}}
example (i : Index R) (n : ℕ) :
    (boundedAboveFlatCoefficientSectionWaldhausen i).K n ≃*
      (RingedSpace.boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).K n :=
  boundedAboveFlatCoefficientSectionKEquiv i n
example (i : Index R) (S : BoundedAboveFlatCoefficientSections i) :
    boundedAboveFlatCoefficientSectionKEquiv i 0
        ((boundedAboveFlatCoefficientSectionWaldhausen i).kZeroObjectClass S) =
      (RingedSpace.boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).kZeroObjectClass
        ((boundedAboveFlatCoefficientOriginalEvaluation i).obj S) :=
  boundedAboveFlatCoefficientSectionKEquiv_objectClass i S
