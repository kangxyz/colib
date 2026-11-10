/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceTorBaseChange

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

local notation3 (prettyPrint := false) "fX" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "fY" => (SmoothSite.product Y T).hom
local notation3 (prettyPrint := false) "fZ" => (SmoothSite.product Z T).hom
local notation3 (prettyPrint := false) "z'" => nativeExteriorPoint X Y T z hz
local notation3 (prettyPrint := false) "w'" => nativeExteriorPoint Y Z T w hw
local notation3 (prettyPrint := false) "I'" => nativeExteriorIncidence X Y Z T z w hz hw
local notation3 (prettyPrint := false) "I₀" =>
  correspondenceIncidence X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "Q" => nativeExteriorParameterDiagonal X Y T z hz Z w hw
local notation3 (prettyPrint := false) "c" =>
  nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw
local notation3 (prettyPrint := false) "π" => nativeExteriorIncidenceOriginal X Y Z T z w hz hw
local notation3 (prettyPrint := false) "a" =>
  correspondenceIncidenceAmbientInclusion fX fY fZ z' w'
local notation3 (prettyPrint := false) "R" =>
  correspondenceIncidenceAmbientStalk fX fY fZ z' w' x
local notation3 (prettyPrint := false) "D" => (Q).presheaf.stalk (c x)
local notation3 (prettyPrint := false) "E₀" => (I₀).presheaf.stalk (π x)
local notation3 (prettyPrint := false) "E" => (I').presheaf.stalk x
local notation3 (prettyPrint := false) "η" => ((c).stalkMap x).hom
local notation3 (prettyPrint := false) "p" => ((π).stalkMap x).hom
local notation3 (prettyPrint := false) "κ" =>
  nativeExteriorTorCoefficientStalkMap X Y Z T z w hz hw x
local notation3 (prettyPrint := false) "T'" =>
  correspondenceIncidenceAmbientTor fX fY fZ z' w' x
local notation3 (prettyPrint := false) "T₀" =>
  correspondenceIncidenceAmbientTor X.hom Y.hom Z.hom z w (π x)

-- The stated all-degree endpoint uses both native incidence module structures.
example (n : ℕ) :
    let : Algebra E₀ E := (p).toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    let := correspondenceIncidenceTorModule fX fY fZ z' w' x n
    Nonempty (T' n ≃ₗ[E] E ⊗[E₀] T₀ n) :=
  ⟨nativeExteriorIncidenceTorBaseChangeEquiv X Y Z T z w hz hw x n⟩

-- Degree zero is included; no positive-degree restriction is hidden in the comparison.
example :
    let : Algebra E₀ E := (p).toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) 0
    let := correspondenceIncidenceTorModule fX fY fZ z' w' x 0
    Nonempty (T' 0 ≃ₗ[E] E ⊗[E₀] T₀ 0) :=
  ⟨nativeExteriorIncidenceTorBaseChangeEquiv X Y Z T z w hz hw x 0⟩

-- Arbitrary actual incidence scalars, rather than a replacement coefficient action.
example (n : ℕ) (e : E) (t : T' n) :
    let : Algebra E₀ E := (p).toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    let := correspondenceIncidenceTorModule fX fY fZ z' w' x n
    nativeExteriorIncidenceTorBaseChangeEquiv X Y Z T z w hz hw x n (e • t) =
      e • nativeExteriorIncidenceTorBaseChangeEquiv X Y Z T z w hz hw x n t :=
  nativeExteriorIncidenceTorBaseChangeEquiv_map_smul X Y Z T z w hz hw x n e t

-- The already existing ambient action is carried through the literal ambient stalk map.
example (n : ℕ) (r : R) (t : T' n) :
    let : Algebra E₀ E := (p).toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    let := correspondenceIncidenceTorModule fX fY fZ z' w' x n
    nativeExteriorIncidenceTorBaseChangeEquiv X Y Z T z w hz hw x n (r • t) =
      ((a).stalkMap x).hom r •
        nativeExteriorIncidenceTorBaseChangeEquiv X Y Z T z w hz hw x n t :=
  nativeExteriorIncidenceTorBaseChangeEquiv_ambient_smul X Y Z T z w hz hw x n r t

-- Both directions recover the actual native Tor element.
example (n : ℕ) (t : T' n) :
    let : Algebra E₀ E := (p).toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
    let := correspondenceIncidenceTorModule fX fY fZ z' w' x n
    (nativeExteriorIncidenceTorBaseChangeEquiv X Y Z T z w hz hw x n).symm
      (nativeExteriorIncidenceTorBaseChangeEquiv X Y Z T z w hz hw x n t) = t := by
  let : Algebra E₀ E := (p).toAlgebra
  let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
  let := correspondenceIncidenceTorModule fX fY fZ z' w' x n
  exact (nativeExteriorIncidenceTorBaseChangeEquiv X Y Z T z w hz hw x n).symm_apply_apply t

-- Positive Tor is retained, without a coefficient regularity or vanishing premise.
example (n : ℕ) :
    let : Algebra E₀ E := (p).toAlgebra
    let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) (n + 1)
    let := correspondenceIncidenceTorModule fX fY fZ z' w' x (n + 1)
    Nonempty (T' (n + 1) ≃ₗ[E] E ⊗[E₀] T₀ (n + 1)) :=
  ⟨nativeExteriorIncidenceTorBaseChangeEquiv X Y Z T z w hz hw x (n + 1)⟩
