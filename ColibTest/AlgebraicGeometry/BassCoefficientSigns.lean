module

public import Colib.AlgebraicGeometry.ProjectiveLine.LaurentOverlapCoefficientBoundary
public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateUnitPair
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientForwardQuotient
public import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine

attribute [local instance] HasDerivedCategory.standard

universe u

#check laurentMinus_rangeRestrictGlobalUnit
#check laurentMinus_forward_coefficient_boundary
#check laurentMinus_opensRange_eq_affineOverlap
#check positiveBassUnitSection_coordinates
#check positiveBassForwardUnit_coordinates
#check positiveBassBoundedFlatForwardUnit_coordinates
#check positiveBassBoundedFlatInverseUnit_coordinates
#check coefficientAmbientForwardUnitQuotient_eq_neg_inv

set_option backward.isDefEq.respectTransparency false in
example :
    let R := CommRingCat.of (ZMod 1)
    let X : QuasiCompactSchemes := ⟨Spec R, inferInstanceAs (CompactSpace (Spec R))⟩
    let f := (Relative.polynomialSpecIso R).hom ≫ (standardChartPolynomialIso X 1).inv
    (laurentMinus R).opensRange = f ⁻¹ᵁ chartOverlap X.obj :=
  laurentMinus_opensRange_eq_affineOverlap _

set_option backward.isDefEq.respectTransparency false in
example (R : CommRingCat.{u}) (K : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := (Spec (.of (Polynomial R))).toRingedSpace))) :
    let i := laurentMinus R
    let j := i.opensRange.ι
    let q := Units.map i.isoOpensRange.inv.appTop.hom.toMonoidHom (laurentCoordinate R)
    letI := laurentMinus_compactSpaceOpensRange R
    perfectQcqsConnectingHom j 0
      (KMap (perfectComplexesRestrictOpenImmersion_isExact i.isoOpensRange.inv) 1
        (perfectGlobalUnitKOneClass _ (laurentCoordinate R)
          ((perfectComplexesRestrictOpenImmersion i).obj K))) =
      ((perfectSupportedWaldhausen j).kZeroObjectClass
        ((perfectAcyclicToSupported j).obj
          (perfectOpenScalarCone (polynomialCoordinate R) j q⁻¹
            (laurentMinus_opensRange_coordinate R) K)))⁻¹ :=
  laurentMinus_forward_coefficient_boundary R K

#print axioms laurentMinus_forward_coefficient_boundary
#print axioms laurentMinus_opensRange_eq_affineOverlap
#print axioms positiveBassUnitSection_coordinates
#print axioms positiveBassForwardUnit_coordinates
#print axioms positiveBassBoundedFlatForwardUnit_coordinates
#print axioms positiveBassBoundedFlatInverseUnit_coordinates
#print axioms positiveBassAdditiveCokernelBoundary_π
#print axioms coefficientAmbientPositiveBassBoundaryIso_π
#print axioms coefficientAmbientForwardUnitQuotient_eq_neg_inv
