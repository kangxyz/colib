/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.OriginalTorKoszul

/-!
# Actual-point consumers for the original remaining-list Tor comparison

SOURCE_ONLY_UNCOMPILED. These examples use a genuine native exterior incidence
point, its original native ambient Tor and the constructed remaining family.
No regular-list provider, coefficient regularity, support flatness or supplied
Tor equivalence is a hypothesis. They have not been elaborated or executed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open AlgebraicGeometry.Scheme
open Stacks.Chow

universe u

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)
  (x : nativeExteriorIncidence X Y Z T z w hz hw)

local notation3 (prettyPrint := false) "P₀" =>
  correspondenceSupportProduct X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "c" =>
  nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw
local notation3 (prettyPrint := false) "q" =>
  nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw
local notation3 (prettyPrint := false) "π" => nativeExteriorIncidenceOriginal X Y Z T z w hz hw
local notation3 (prettyPrint := false) "C₀" => (P₀).presheaf.stalk (q (c x))
local notation3 (prettyPrint := false) "T₀" =>
  correspondenceIncidenceAmbientTor X.hom Y.hom Z.hom z w (π x)
local notation3 (prettyPrint := false) "F" =>
  nativeExteriorRemainingStalkFamily X Y T z hz Z w hw x
local notation3 (prettyPrint := false) "η₀" =>
  (nativeExteriorRemainingOriginalIncidenceStalkMap X Y T z hz Z w hw x).hom

example :
    let e := nativeExteriorOriginalTorMiddleStalkIso X Y Z T z w hz hw x
    let t := fun j => e.hom.hom ((F).baseList.get j)
    let y := correspondenceMiddlePair X.hom Y.hom Z.hom
      (correspondenceIncidenceAmbientInclusion X.hom Y.hom Z.hom z w (π x))
    IsRegular ((pullback Y.hom Y.hom).presheaf.stalk y) (List.ofFn t) ∧
      IdealSheafData.stalk (pullback.diagonal Y.hom).ker y = Ideal.span (Set.range t) :=
  correspondenceOriginalMiddleList_stalkCongr X.hom Y.hom Z.hom z w (π x)
    _ (nativeExteriorOriginalTor_middlePoint X Y Z T z w hz hw x)
    (F).baseList (F).base_regular (F).base_ideal

example (n : ℕ) :
    let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
    T₀ n ≃ₗ[C₀]
      ((Koszul.seqComplexTensor
        (fun j => nativeExteriorOriginalTorMiddleStalkMap X Y Z T z w hz hw x
          ((F).baseList.get j)) C₀).homology n) :=
  correspondenceIncidenceTorSupportLinearEquivOfPoints X.hom Y.hom Z.hom z w (π x)
    (q (c x)) (nativeExteriorIncidenceQuotient_point X Y Z T z w hz hw x).symm
    _ (nativeExteriorOriginalTor_middlePoint X Y Z T z w hz hw x)
    (F).baseList (F).base_regular (F).base_ideal n
