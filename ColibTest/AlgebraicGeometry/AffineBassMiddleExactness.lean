module

public import Colib.AlgebraicGeometry.ProjectiveLine.AffineBassMiddleExactness
public import Colib.AlgebraicGeometry.KTheory.PerfectPullback
public import Colib.AlgebraicGeometry.ProjectiveLine.AffineLaurentRankOne
public import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.ProjectiveLine

attribute [local instance] Waldhausen.Additivity.KCommGroup

example (R : CommRingCat) :
    ((perfectKPullback (PolynomialLaurent.polynomialProjection R) 0).prod
      (perfectKPullback (PolynomialLaurent.polynomialProjection R) 0)).range =
    (GroupMayerVietoris.difference (perfectKPullback (laurentToPolynomial R) 0)
      (perfectKPullback (laurentMinus R) 0)).ker :=
  affineBass_coefficientPair_range_eq_ker R 0

example :
    let R := CommRingCat.of (ZMod 1)
    ((perfectKPullback (PolynomialLaurent.polynomialProjection R) 0).prod
      (perfectKPullback (PolynomialLaurent.polynomialProjection R) 0)).range =
    (GroupMayerVietoris.difference (perfectKPullback (laurentToPolynomial R) 0)
      (perfectKPullback (laurentMinus R) 0)).ker :=
  affineBass_coefficientPair_range_eq_ker _ 0

set_option backward.isDefEq.respectTransparency false in
example (R : CommRingCat) :
    let X : QuasiCompactSchemes := ⟨Spec R, inferInstanceAs (CompactSpace (Spec R))⟩
    let B : Spec (.of (LaurentPolynomial R)) ≅ (Relative.laurentFunctor.obj X).obj :=
      Relative.laurentSpecIso R
    let W := RingedSpace.perfectComplexesWaldhausen (Spec R).toRingedSpace
    positiveBassBoundary X 0
        (perfectKPullback B.inv 1
          (perfectOpenKRestrict (laurentToPolynomial R) 1
            (perfectScalarForwardKOneClass (laurentToPolynomial R)
              (rankOnePerfectComplex (Spec (.of (Polynomial R)))) (polynomialCoordinate R)
              (laurentCoordinate R) (laurentToPolynomial_appTop_coordinate R)))) =
      (W.kZeroObjectClass (rankOnePerfectComplex (Spec R)))⁻¹ :=
  affinePositiveBassBoundary_polynomialScalarForward_rankOne R

#print axioms affineBass_coefficientPair_range_eq_ker
#print axioms perfectNegativeTwistCoordinateCone_rankOne_class
#print axioms connectingHom_forwardCoordinateUnit_rankOne
#print axioms affineConnectingCoefficients_forward_rankOne
#print axioms affinePositiveBassBoundary_forward_rankOne
#print axioms affinePositiveBassBoundary_polynomialScalarForward_rankOne
