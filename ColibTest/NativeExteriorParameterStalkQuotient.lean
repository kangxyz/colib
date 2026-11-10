module

import Colib.AlgebraicGeometry.Correspondences.Exterior.ParameterStalkQuotient

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open AlgebraicGeometry.Scheme

noncomputable section
universe u
variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

local notation3 "Q" => nativeExteriorParameterDiagonal X Y T z hz Z w hw
local notation3 "j" => nativeExteriorParameterDiagonalInclusion X Y T z hz Z w hw
local notation3 "P" =>
  correspondenceSupportProduct (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
    (SmoothSite.product Z T).hom (nativeExteriorPoint X Y T z hz)
    (nativeExteriorPoint Y Z T w hw)

example (x : Q) :
    ((P).presheaf.stalk (j x) ⧸ nativeExteriorParameterStalkIdeal X Y T z hz Z w hw x) ≃+*
      (Q).presheaf.stalk x :=
  nativeExteriorParameterStalkQuotientEquiv X Y T z hz Z w hw x

example (x : Q) (r : (P).presheaf.stalk (j x)) :
    nativeExteriorParameterStalkQuotientEquiv X Y T z hz Z w hw x (Ideal.Quotient.mk _ r) =
      ((j).stalkMap x).hom r :=
  nativeExteriorParameterStalkQuotientEquiv_mk X Y T z hz Z w hw x r

example (x : Q) : ∃ rs : List ((P).presheaf.stalk (j x)),
    RingTheory.Sequence.IsRegular ((P).presheaf.stalk (j x)) rs ∧
      Ideal.ofList rs = nativeExteriorParameterStalkIdeal X Y T z hz Z w hw x :=
  nativeExteriorParameterStalkIdeal_exists_regular X Y T z hz Z w hw x

example (x : Q) : RingHom.ker ((j).stalkMap x).hom =
    nativeExteriorParameterStalkIdeal X Y T z hz Z w hw x :=
  nativeExteriorParameterDiagonal_stalkMap_ker X Y T z hz Z w hw x

example : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion j :=
  nativeExteriorParameterDiagonalInclusion_regular X Y T z hz Z w hw

example (x : Q) :
    ((nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw).stalkMap x).hom.Flat :=
  nativeExteriorCoefficientQuotientProjection_stalkMap_flat X Y T z hz Z w hw x
