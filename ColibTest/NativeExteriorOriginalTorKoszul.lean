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

example (n : ℕ) :
    let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
    T₀ n ≃ₗ[C₀]
      ((Koszul.seqComplexTensor (F).originalCoefficientList.get C₀).homology n) :=
  nativeExteriorOriginalTorRemainingKoszulEquiv X Y Z T z w hz hw x n

example :
    let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x 0
    T₀ 0 ≃ₗ[C₀]
      ((Koszul.seqComplexTensor (F).originalCoefficientList.get C₀).homology 0) :=
  nativeExteriorOriginalTorRemainingKoszulEquiv X Y Z T z w hz hw x 0

example (n : ℕ) (a : C₀) (t : T₀ n) :
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
    nativeExteriorOriginalTorRemainingKoszulEquiv X Y Z T z w hz hw x n ((η₀) a • t) =
      a • nativeExteriorOriginalTorRemainingKoszulEquiv X Y Z T z w hz hw x n t := by
  let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
  let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
  dsimp only
  exact nativeExteriorOriginalTorRemainingKoszulEquiv_map_smul X Y Z T z w hz hw x n a t

example (n : ℕ) (t : T₀ n) :
    let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
    (nativeExteriorOriginalTorRemainingKoszulEquiv X Y Z T z w hz hw x n).symm
      (nativeExteriorOriginalTorRemainingKoszulEquiv X Y Z T z w hz hw x n t) = t :=
  nativeExteriorOriginalTorRemainingKoszulEquiv_symm_apply_apply X Y Z T z w hz hw x n t

example (n : ℕ)
    (t : (Koszul.seqComplexTensor (F).originalCoefficientList.get C₀).homology n) :
    let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
    nativeExteriorOriginalTorRemainingKoszulEquiv X Y Z T z w hz hw x n
      ((nativeExteriorOriginalTorRemainingKoszulEquiv X Y Z T z w hz hw x n).symm t) = t := by
  let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
  exact (nativeExteriorOriginalTorRemainingKoszulEquiv X Y Z T z w hz hw x n).apply_symm_apply t
