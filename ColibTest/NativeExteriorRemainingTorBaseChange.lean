/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.RemainingTorBaseChange

/-!
# Actual-point and actual-scalar consumers

These examples retain the actual full incidence points,
original native Tor, native incidence actions, and the literal stalk maps.
No comparison, regularity, flatness or vanishing is supplied by the consumer.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open AlgebraicGeometry.Scheme
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)
  (x : nativeExteriorIncidence X Y Z T z w hz hw)

local notation3 (prettyPrint := false) "I'" => nativeExteriorIncidence X Y Z T z w hz hw
local notation3 (prettyPrint := false) "I₀" =>
  correspondenceIncidence X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "P₀" =>
  correspondenceSupportProduct X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "Q" => nativeExteriorParameterDiagonal X Y T z hz Z w hw
local notation3 (prettyPrint := false) "c" =>
  nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw
local notation3 (prettyPrint := false) "q" =>
  nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw
local notation3 (prettyPrint := false) "π" => nativeExteriorIncidenceOriginal X Y Z T z w hz hw
local notation3 (prettyPrint := false) "C₀" => (P₀).presheaf.stalk (q (c x))
local notation3 (prettyPrint := false) "D" => (Q).presheaf.stalk (c x)
local notation3 (prettyPrint := false) "E₀" => (I₀).presheaf.stalk (π x)
local notation3 (prettyPrint := false) "E" => (I').presheaf.stalk x
local notation3 (prettyPrint := false) "α" => ((q).stalkMap (c x)).hom
local notation3 (prettyPrint := false) "η" => ((c).stalkMap x).hom
local notation3 (prettyPrint := false) "p" => ((π).stalkMap x).hom
local notation3 (prettyPrint := false) "T₀" =>
  correspondenceIncidenceAmbientTor X.hom Y.hom Z.hom z w (π x)
local notation3 (prettyPrint := false) "F" =>
  nativeExteriorRemainingStalkFamily X Y T z hz Z w hw x
local notation3 (prettyPrint := false) "H₀" =>
  Koszul.seqComplexTensor (F).originalCoefficientList.get (ModuleCat.of C₀ C₀)
local notation3 (prettyPrint := false) "HD" =>
  Koszul.seqComplexTensor (F).coefficientList.get (ModuleCat.of D D)

-- The endpoint is genuinely D-linear and uses original native Tor.
example (n : ℕ) :
    let : Algebra E₀ E := (p).toAlgebra
    let : Algebra D E := (η).toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    Nonempty ((HD).homology n ≃ₗ[D] E ⊗[E₀] T₀ n) :=
  ⟨nativeExteriorRemainingKoszulIncidenceBaseChangeEquiv X Y Z T z w hz hw x n⟩

-- Every actual D scalar acts through the actual incidence quotient on the target.
example (n : ℕ) (d : D) (h : (HD).homology n) :
    let : Algebra E₀ E := (p).toAlgebra
    let : Algebra D E := (η).toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    nativeExteriorRemainingKoszulIncidenceBaseChangeEquiv X Y Z T z w hz hw x n (d • h) =
      (η) d • nativeExteriorRemainingKoszulIncidenceBaseChangeEquiv
        X Y Z T z w hz hw x n h := by
  let : Algebra E₀ E := (p).toAlgebra
  let : Algebra D E := (η).toAlgebra
  let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
  rw [LinearEquiv.map_smul]
  exact (IsScalarTower.algebraMap_smul E _ _).symm

-- The tensor generator uses the literal original Tor comparison and actual η.
example (n : ℕ) (d : D) (t : T₀ n) :
    let : Algebra C₀ D := (α).toAlgebra
    let : Algebra E₀ E := (p).toAlgebra
    let : Algebra D E := (η).toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    let := nativeExteriorOriginalTorCoefficientModule X Y Z T z w hz hw x n
    nativeExteriorRemainingKoszulIncidenceBaseChangeEquiv X Y Z T z w hz hw x n
      ((nativeExteriorRemainingKoszulHomologyBaseChangeEquiv X Y Z T z w hz hw x n).symm
        (d ⊗ₜ[C₀]
          nativeExteriorOriginalTorRemainingKoszulEquiv X Y Z T z w hz hw x n t)) =
      (η) d ⊗ₜ[E₀] t :=
  nativeExteriorRemainingKoszulIncidenceBaseChangeEquiv_tmul X Y Z T z w hz hw x n d t
