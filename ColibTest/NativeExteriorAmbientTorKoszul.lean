/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.AmbientTorKoszul

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
  (z : pullback («C» := Scheme) X.hom Y.hom)
  (w : pullback («C» := Scheme) Y.hom Z.hom)
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

local notation3 (prettyPrint := false) "B" => (QA).presheaf.stalk (iQ (c x))
local notation3 (prettyPrint := false) "C" => (P).presheaf.stalk (j (c x))
local notation3 (prettyPrint := false) "L" => (V).presheaf.stalk (v x)
local notation3 (prettyPrint := false) "θ" => ((iQ).stalkMap (c x)).hom
local notation3 (prettyPrint := false) "e" =>
  nativeExteriorTorAmbientStalkIso X Y Z T z w hz hw x
local notation3 (prettyPrint := false) "κ" =>
  nativeExteriorTorCoefficientStalkMap X Y Z T z w hz hw x
local notation3 (prettyPrint := false) "F" =>
  nativeExteriorRemainingStalkFamily X Y T z hz Z w hw x
local notation3 (prettyPrint := false) "T'" =>
  correspondenceIncidenceAmbientTor fX fY fZ z' w' x
local notation3 (prettyPrint := false) "H" =>
  Koszul.seqComplexTensor (F).coefficientList.get (ModuleCat.of D D)

-- The full native endpoint, with its actual ambient scalar map.
example (n : ℕ) : Nonempty (T' n ≅ (ModuleCat.restrictScalars κ).obj ((H).homology n)) :=
  ⟨nativeExteriorAmbientTorRemainingKoszulIso X Y Z T z w hz hw x n⟩

-- Degree zero is included; this is not a positive-Tor-vanishing statement.
example : Nonempty (T' 0 ≅ (ModuleCat.restrictScalars κ).obj ((H).homology 0)) :=
  ⟨nativeExteriorAmbientTorRemainingKoszulIso X Y Z T z w hz hw x 0⟩

-- Positive homology is retained, not assumed to vanish.
example (n : ℕ) :
    Nonempty (T' (n + 1) ≅ (ModuleCat.restrictScalars κ).obj ((H).homology (n + 1))) :=
  ⟨nativeExteriorAmbientTorRemainingKoszulIso X Y Z T z w hz hw x (n + 1)⟩

-- Inverse recovery occurs on the native Tor object, not on a replacement model.
example (n : ℕ) (m : T' n) :
    (nativeExteriorAmbientTorRemainingKoszulIso X Y Z T z w hz hw x n).inv
      ((nativeExteriorAmbientTorRemainingKoszulIso X Y Z T z w hz hw x n).hom m) = m :=
  (nativeExteriorAmbientTorRemainingKoszulIso X Y Z T z w hz hw x n).toLinearEquiv.symm_apply_apply m

-- The target action is visibly κ(a) acting through its original D-module structure.
example (n : ℕ) (r₀ : Rₙ) (m : T' n) :
    (nativeExteriorAmbientTorRemainingKoszulIso X Y Z T z w hz hw x n).hom (r₀ • m) =
      (κ) r₀ • (nativeExteriorAmbientTorRemainingKoszulIso X Y Z T z w hz hw x n).hom m :=
  (nativeExteriorAmbientTorRemainingKoszulIso X Y Z T z w hz hw x n).hom.hom.map_smul r₀ m

-- The functional endpoint uses precisely the literal coefficient list and order.
example : H = Koszul.seqComplexTensor (fun idx => (θ) ((F).ambientList.get idx))
    (ModuleCat.of D D) :=
  nativeExteriorRemainingCoefficient_complex_eq X Y Z T z w hz hw x

-- The coefficient action followed by the incidence map recovers the native ambient action.
example (a₀ : Rₙ) :
    ((c).stalkMap x).hom ((κ) a₀) = ((a).stalkMap x).hom a₀ :=
  congrArg (fun ρ => ρ a₀)
    (nativeExteriorTorCoefficientStalkMap_incidence X Y Z T z w hz hw x)
