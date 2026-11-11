/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.AmbientTorStalkMaps

/-!
# Actual exterior ambient Tor reduction consumers

SOURCE_ONLY_UNCOMPILED. All examples use a point of the genuine native exterior
incidence and the one constructed remaining family. No regularity, tensor
quotient, Tor vanishing, comparison, or coefficient flatness is a caller input.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)
  (x : nativeExteriorIncidence X Y Z T z w hz hw)

local notation3 (prettyPrint := false) "fX" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "fY" => (SmoothSite.product Y T).hom
local notation3 (prettyPrint := false) "fZ" => (SmoothSite.product Z T).hom
local notation3 (prettyPrint := false) "z'" => nativeExteriorPoint X Y T z hz
local notation3 (prettyPrint := false) "w'" => nativeExteriorPoint Y Z T w hw
local notation3 (prettyPrint := false) "I'" => nativeExteriorIncidence X Y Z T z w hz hw
local notation3 (prettyPrint := false) "A" => correspondenceIntersectionAmbient fX fY fZ
local notation3 (prettyPrint := false) "P" => correspondenceSupportProduct fX fY fZ z' w'
local notation3 (prettyPrint := false) "V" => correspondenceTripleProduct fX fY fZ
local notation3 (prettyPrint := false) "Q" => nativeExteriorParameterDiagonal X Y T z hz Z w hw
local notation3 (prettyPrint := false) "QA" => exteriorAmbientParameterQuotient X Y Z T
local notation3 (prettyPrint := false) "a" =>
  correspondenceIncidenceAmbientInclusion fX fY fZ z' w'
local notation3 (prettyPrint := false) "b" =>
  correspondenceIncidenceToSupportProduct fX fY fZ z' w'
local notation3 (prettyPrint := false) "i" =>
  correspondenceSupportProductInclusion fX fY fZ z' w'
local notation3 (prettyPrint := false) "v" =>
  correspondenceIncidenceInclusion fX fY fZ z' w'
local notation3 (prettyPrint := false) "t" => correspondenceTripleInclusion fX fY fZ
local notation3 (prettyPrint := false) "j" =>
  nativeExteriorParameterDiagonalInclusion X Y T z hz Z w hw
local notation3 (prettyPrint := false) "jA" => exteriorAmbientParameterInclusion X Y Z T
local notation3 (prettyPrint := false) "iQ" =>
  nativeExteriorCoefficientQuotientInclusion X Y T z hz Z w hw
local notation3 (prettyPrint := false) "c" =>
  nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw
local notation3 (prettyPrint := false) "l" => exteriorAmbientRemainingInclusion X Y Z T
local notation3 (prettyPrint := false) "Rₙ" =>
  correspondenceIncidenceAmbientStalk fX fY fZ z' w' x
local notation3 (prettyPrint := false) "R" => (A).presheaf.stalk (i (j (c x)))
local notation3 (prettyPrint := false) "D" => (Q).presheaf.stalk (c x)
local notation3 (prettyPrint := false) "f" =>
  (nativeExteriorAmbientParameterStalkMap X Y T z hz Z w hw (c x)).hom
local notation3 (prettyPrint := false) "g" =>
  (nativeExteriorRemainingAmbientStalkMap X Y T z hz Z w hw x).hom
local notation3 (prettyPrint := false) "φ" => ((i).stalkMap (j (c x))).hom
local notation3 (prettyPrint := false) "ψ" => ((j).stalkMap (c x)).hom

example : j (c x) = b x := nativeExteriorTor_supportPoint X Y Z T z w hz hw x

example : Nonempty (Rₙ ≃+* R) :=
  ⟨(nativeExteriorTorAmbientStalkIso X Y Z T z w hz hw x).commRingCatIsoToRingEquiv⟩

example :
    (nativeExteriorTorAmbientStalkIso X Y Z T z w hz hw x).hom ≫
        (i).stalkMap (j (c x)) ≫
          ((P).presheaf.stalkCongr
            (.of_eq (nativeExteriorTor_supportPoint X Y Z T z w hz hw x))).hom =
      ((A).presheaf.stalkCongr
        (.of_eq (correspondenceIncidence_ambient_point_eq fX fY fZ z' w' x))).hom ≫
          (i).stalkMap (b x) :=
  correspondenceIncidenceAmbientStalkIsoOfSupportPoint_support fX fY fZ z' w' x
    (j (c x)) (nativeExteriorTor_supportPoint X Y Z T z w hz hw x)

example (a₀ : Rₙ) :
    ((t).stalkMap (v x)).hom a₀ =
      (g) ((f) ((nativeExteriorTorAmbientStalkIso X Y Z T z w hz hw x).hom.hom a₀)) :=
  congrArg (fun ρ => ρ a₀) (nativeExteriorTor_tripleStalkMap X Y Z T z w hz hw x)
