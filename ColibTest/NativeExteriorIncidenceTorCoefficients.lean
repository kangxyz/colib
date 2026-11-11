/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceTorCoefficients

/-!
# Actual generic-point consumers of exterior Tor coefficients

The examples use the existing native ambient Tor and signed coefficients. Their
finiteness is supplied by the original generic Tor theorem, not by a new premise.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

local notation3 (prettyPrint := false) "fX" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "fY" => (SmoothSite.product Y T).hom
local notation3 (prettyPrint := false) "fZ" => (SmoothSite.product Z T).hom
local notation3 (prettyPrint := false) "z'" => nativeExteriorPoint X Y T z hz
local notation3 (prettyPrint := false) "w'" => nativeExteriorPoint Y Z T w hw
local notation3 (prettyPrint := false) "I'" => nativeExteriorIncidence X Y Z T z w hz hw
local notation3 (prettyPrint := false) "I₀" =>
  correspondenceIncidence X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "π" =>
  nativeExteriorIncidenceOriginal X Y Z T z w hz hw
local notation3 (prettyPrint := false) "G" =>
  nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw

example (x : I') (hx : x ∈ genericPoints I') (n : ℕ) :
    Module.length (correspondenceIncidenceAmbientStalk fX fY fZ z' w' x)
      (correspondenceIncidenceAmbientTor fX fY fZ z' w' x n) =
    Module.length (correspondenceIncidenceAmbientStalk X.hom Y.hom Z.hom z w (π x))
      (correspondenceIncidenceAmbientTor X.hom Y.hom Z.hom z w (π x) n) :=
  nativeExteriorIncidenceTor_length_eq_original X Y Z T z w hz hw x hx n

example (η : genericPoints I₀) (n : ℕ) :
    Module.length (correspondenceIncidenceAmbientStalk fX fY fZ z' w' (G η).val)
      (correspondenceIncidenceAmbientTor fX fY fZ z' w' (G η).val n) =
    Module.length (correspondenceIncidenceAmbientStalk X.hom Y.hom Z.hom z w η.val)
      (correspondenceIncidenceAmbientTor X.hom Y.hom Z.hom z w η.val n) :=
  nativeExteriorIncidenceGenericTor_length X Y Z T z w hz hw η n

example (η : genericPoints I₀) :
    correspondenceIncidenceTorTerm k fX fY fZ z' w' (G η) 0 =
      correspondenceIncidenceTorTerm k X.hom Y.hom Z.hom z w η 0 :=
  correspondenceIncidenceTorTerm_nativeExterior X Y Z T z w hz hw η 0

example (η : genericPoints I₀) (n : ℕ) :
    correspondenceIncidenceTorTerm k fX fY fZ z' w' (G η) n =
      correspondenceIncidenceTorTerm k X.hom Y.hom Z.hom z w η n :=
  correspondenceIncidenceTorTerm_nativeExterior X Y Z T z w hz hw η n

example (η : genericPoints I₀) :
    correspondenceIncidenceTorCoefficient k fX fY fZ z' w' (G η) =
      correspondenceIncidenceTorCoefficient k X.hom Y.hom Z.hom z w η :=
  correspondenceIncidenceTorCoefficient_nativeExterior X Y Z T z w hz hw η

example (η : genericPoints I₀) (n : ℕ) :
    Module.length (correspondenceIncidenceAmbientStalk X.hom Y.hom Z.hom z w η.val)
      (correspondenceIncidenceAmbientTor X.hom Y.hom Z.hom z w η.val n) ≠ ⊤ :=
  correspondenceIncidenceTor_length_ne_top
    (show X.left ⟶ Spec (.of k) from X.hom) Y.hom Z.hom z w η n

example (η : genericPoints I₀) (n : ℕ) :
    Module.length (correspondenceIncidenceAmbientStalk fX fY fZ z' w' (G η).val)
      (correspondenceIncidenceAmbientTor fX fY fZ z' w' (G η).val n) ≠ ⊤ :=
  correspondenceIncidenceTor_length_ne_top
    (show (SmoothSite.product X T).left ⟶ Spec (.of k) from fX) fY fZ z' w' (G η) n
