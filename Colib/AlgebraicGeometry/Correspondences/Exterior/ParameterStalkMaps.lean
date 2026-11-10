/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.AmbientParameterRegular
public import Colib.AlgebraicGeometry.Correspondences.Exterior.CoefficientAmbient
public import Colib.AlgebraicGeometry.Correspondences.Exterior.ParameterStalkQuotient

/-!
# Literal scalar and quotient maps at an exterior parameter point

Let `x` be a point of the actual coefficient parameter quotient. Write `P`
for the exterior support product, `A` for the original exterior ambient,
`j : Q ⟶ P` and `jA : QA ⟶ A` for the two parameter inclusions, and
`i : P ⟶ A`, `iQ : Q ⟶ QA` for the actual support inclusions.

The common ambient local ring is taken at `i (j x)`. The target of the
ambient quotient map is the actual stalk at `iQ x`; its only adjustment
is Mathlib's `stalkCongr` along `i (j x) = jA (iQ x)`.
The coefficient parameter map likewise retains the equality between its
actual base point and the ambient parameter base point. The scalar square,
both quotient kernels and surjectivity refer to these literal maps.

No replacement local ring or independently selected family is introduced.
Native suppliers: Mathlib `Scheme.Hom.stalkMap_congr_hom` and `stalkMap_comp`;
Stacks `IdealSheafData.stalk_comap` and `ker_stalkMap_eq_idealStalk_ker`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (Z : SmoothSite (Spec (.of k)))
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

local notation3 (prettyPrint := false) "A" => correspondenceIntersectionAmbient
  (SmoothSite.product X T).hom (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
local notation3 (prettyPrint := false) "Q" => nativeExteriorParameterDiagonal X Y T z hz Z w hw
local notation3 (prettyPrint := false) "j" =>
  nativeExteriorParameterDiagonalInclusion X Y T z hz Z w hw
local notation3 (prettyPrint := false) "i" => correspondenceSupportProductInclusion
  (SmoothSite.product X T).hom (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
  (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)
local notation3 (prettyPrint := false) "a" => exteriorAmbientParameterPair X Y Z T
local notation3 (prettyPrint := false) "p" =>
  nativeExteriorCoefficientParameterPair X Y T z hz Z w hw
local notation3 (prettyPrint := false) "jA" => exteriorAmbientParameterInclusion X Y Z T
local notation3 (prettyPrint := false) "iQ" =>
  nativeExteriorCoefficientQuotientInclusion X Y T z hz Z w hw

/-- Equality of the actual ambient points before and after the parameter quotient. -/
theorem nativeExteriorParameter_ambientPoint (x : Q) : i (j x) = jA (iQ x) :=
  congrArg (fun f : Q ⟶ A => f x)
    (nativeExteriorCoefficientQuotientInclusion_ambient X Y T z hz Z w hw).symm

/-- Equality of the actual two descriptions of the parameter base point. -/
theorem nativeExteriorParameter_basePoint (x : Q) : a (i (j x)) = p (j x) :=
  congrArg (fun f => f (j x))
    (nativeExteriorCoefficientParameterPair_ambient X Y T z hz Z w hw)

/-- The ambient quotient map with its true source and target stalks identified. -/
def nativeExteriorAmbientParameterStalkMap (x : Q) :
    (A).presheaf.stalk (i (j x)) ⟶
      (exteriorAmbientParameterQuotient X Y Z T).presheaf.stalk (iQ x) :=
  ((A).presheaf.stalkCongr
    (.of_eq (nativeExteriorParameter_ambientPoint X Y T z hz Z w hw x))).hom ≫
      (jA).stalkMap (iQ x)

/-- The actual coefficient parameter stalk map, with its base point identified. -/
def nativeExteriorCoefficientParameterStalkMap (x : Q) :
    (pullback T.hom T.hom).presheaf.stalk (a (i (j x))) ⟶
      (correspondenceSupportProduct (SmoothSite.product X T).hom
        (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
        (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)).presheaf.stalk
          (j x) :=
  ((pullback T.hom T.hom).presheaf.stalkCongr
    (.of_eq (nativeExteriorParameter_basePoint X Y T z hz Z w hw x))).hom ≫
      (p).stalkMap (j x)

/-- The coefficient scalar map is the literal composite of ambient and support stalk maps. -/
theorem nativeExteriorCoefficientParameterStalkMap_eq (x : Q) :
    nativeExteriorCoefficientParameterStalkMap X Y T z hz Z w hw x =
      (a).stalkMap (i (j x)) ≫ (i).stalkMap (j x) := by
  simpa only [nativeExteriorCoefficientParameterStalkMap, Scheme.Hom.stalkMap_comp] using
    (Scheme.Hom.stalkMap_congr_hom (i ≫ a) p
      (nativeExteriorCoefficientParameterPair_ambient X Y T z hz Z w hw) (j x)).symm

/-- The actual quotient square commutes as maps of the specified local rings. -/
theorem nativeExteriorParameter_stalkSquare (x : Q) :
    (i).stalkMap (j x) ≫ (j).stalkMap x =
      nativeExteriorAmbientParameterStalkMap X Y T z hz Z w hw x ≫ (iQ).stalkMap x := by
  simpa only [nativeExteriorAmbientParameterStalkMap, Scheme.Hom.stalkMap_comp,
    Category.assoc] using
    Scheme.Hom.stalkMap_congr_hom (j ≫ i) (iQ ≫ jA)
      (nativeExteriorCoefficientQuotientInclusion_ambient X Y T z hz Z w hw).symm x

/-- The same square in the exact ring-map orientation used by regular-block Tor reduction. -/
theorem nativeExteriorParameter_stalkRingSquare (x : Q) :
    ((j).stalkMap x).hom.comp ((i).stalkMap (j x)).hom =
      ((iQ).stalkMap x).hom.comp
        (nativeExteriorAmbientParameterStalkMap X Y T z hz Z w hw x).hom :=
  congrArg CommRingCat.Hom.hom (nativeExteriorParameter_stalkSquare X Y T z hz Z w hw x)

/-- The transported ambient parameter map is still the surjective closed-immersion map. -/
theorem nativeExteriorAmbientParameterStalkMap_surjective (x : Q) :
    Function.Surjective (nativeExteriorAmbientParameterStalkMap X Y T z hz Z w hw x).hom := by
  let e := (A).presheaf.stalkCongr
    (.of_eq (nativeExteriorParameter_ambientPoint X Y T z hz Z w hw x))
  exact ((jA).stalkMap_surjective (iQ x)).comp e.commRingCatIsoToRingEquiv.surjective

/-- The full ambient kernel, with the point equality transported and no radical taken. -/
theorem nativeExteriorAmbientParameterStalkMap_ker (x : Q) :
    RingHom.ker (nativeExteriorAmbientParameterStalkMap X Y T z hz Z w hw x).hom =
      Ideal.map ((a).stalkMap (i (j x))).hom
        (IdealSheafData.stalk (pullback.diagonal T.hom).ker (a (i (j x)))) := by
  have hker : ∀ (y : A) (e : y = jA (iQ x)),
      RingHom.ker (((A).presheaf.stalkCongr (.of_eq e)).hom ≫ (jA).stalkMap (iQ x)).hom =
        IdealSheafData.stalk (jA).ker y := by
    intro y e
    subst y
    simpa only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
      Category.id_comp] using ker_stalkMap_eq_idealStalk_ker jA (iQ x)
  rw [nativeExteriorAmbientParameterStalkMap,
    hker (i (j x)) (nativeExteriorParameter_ambientPoint X Y T z hz Z w hw x),
    exteriorAmbientParameterInclusion_ker, IdealSheafData.stalk_comap]

/-- The coefficient kernel as the image of the same base ideal through the composite map. -/
theorem nativeExteriorParameterDiagonal_stalkMap_ker_composite (x : Q) :
    RingHom.ker ((j).stalkMap x).hom =
      Ideal.map ((i).stalkMap (j x)).hom
        (Ideal.map ((a).stalkMap (i (j x))).hom
          (IdealSheafData.stalk (pullback.diagonal T.hom).ker (a (i (j x))))) := by
  rw [ker_stalkMap_eq_idealStalk_ker, nativeExteriorParameterDiagonalInclusion_ker,
    ← nativeExteriorCoefficientParameterPair_ambient X Y T z hz Z w hw,
    Scheme.IdealSheafData.comap_comp, IdealSheafData.stalk_comap,
    IdealSheafData.stalk_comap]

/-- The two-flat-map input is derived from the actual coefficient parameter map. -/
theorem nativeExteriorParameter_composite_flat : Flat (i ≫ a) := by
  rw [nativeExteriorCoefficientParameterPair_ambient X Y T z hz Z w hw]
  infer_instance

/-- Literal coefficient images preserve the ambient order, with no permutation. -/
theorem nativeExteriorParameter_map_list (x : Q)
    (l : List ((pullback T.hom T.hom).presheaf.stalk (a (i (j x))))) :
    l.map (nativeExteriorCoefficientParameterStalkMap X Y T z hz Z w hw x).hom =
      (l.map ((a).stalkMap (i (j x))).hom).map ((i).stalkMap (j x)).hom := by
  rw [nativeExteriorCoefficientParameterStalkMap_eq]
  simp only [CommRingCat.hom_comp, List.map_map, RingHom.coe_comp]

end Stacks.Chow
