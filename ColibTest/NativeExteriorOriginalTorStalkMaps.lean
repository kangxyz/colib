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
    nativeExteriorOriginalTorMiddleStalkMap X Y Z T z w hz hw x =
      (nativeExteriorRemainingOriginalStalkMap X Y T z hz Z w hw x).hom :=
  nativeExteriorOriginalTorMiddleStalkMap_eq X Y Z T z w hz hw x

example (j : Fin (F).baseList.length) :
    nativeExteriorOriginalTorMiddleStalkMap X Y Z T z w hz hw x ((F).baseList.get j) =
      (F).originalCoefficientList.get ⟨j.val, by
        simpa only [NativeExteriorRemainingStalkFamily.originalCoefficientList,
          List.length_map] using j.isLt⟩ := by
  rw [nativeExteriorOriginalTorMiddleStalkMap_eq]
  simp only [NativeExteriorRemainingStalkFamily.originalCoefficientList,
    List.get_eq_getElem, List.getElem_map]

example (n : ℕ) (a : C₀) (t : T₀ n) :
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
    a • t = (η₀) a • t :=
  nativeExteriorOriginalTorCoefficientModule_smul X Y Z T z w hz hw x n a t

example (n : ℕ) :
    let E₀ := (correspondenceIncidence X.hom Y.hom Z.hom z w).presheaf.stalk (π x)
    let : Algebra C₀ E₀ := (η₀).toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
    IsScalarTower C₀ E₀ (T₀ n) :=
  nativeExteriorOriginalTorCoefficientScalarTower X Y Z T z w hz hw x n
