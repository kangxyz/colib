/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceTorBaseChange
public import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceGenericLength
public import Colib.AlgebraicGeometry.Correspondences.Composition.ActualTorCoefficients

/-!
# Native exterior Tor lengths and Euler coefficients

Let k be a field and let X, Y, Z, T be smooth-site objects over k, with T
geometrically integral. The actual projection π from the full exterior incidence
to the original incidence preserves ambient Tor lengths at generic points. Both
Tor modules and their quotient-induced incidence actions are the existing native
ones. Scalar extension uses the algebra induced by π.stalkMap at the actual point.

The incidence-linear Tor comparison identifies the exterior module with the
scalar extension of original Tor. Ambient and incidence lengths agree, and the
flat local length formula has closed-fiber length one at a generic point of the
reduced fiber. Its local input is Stacks Tag 02M1, implemented by Mathlib's
IsLocalRing.length_baseChange and the generic-stalk length theorem. The full
incidence schemes are not required to be reduced.

The generic-point equivalence maps ξ to the named original generic point η.
Equality π(ξ) = η transports the complete extended-natural length expression,
including its ambient ring and Tor module. Applying the same integer sign and
toNat, then finsum_congr, gives the existing native Tor term and coefficient.
The original generic Tor finiteness theorem supplies the finite-length meaning
of these coefficients; no equality of dimension cutoffs is needed.

The closed-fiber length is not a residue-field degree. No finite residue degree,
separability, support flatness or regularity of the coefficient sequence is
assumed. No cycle, finite pushforward or exterior-composition theorem is asserted.

Software inputs: Colib e7697ab8164435c7093665d02ac34f021eefb75e,
Composition/PairTorAction.lean:161-172 and ActualTorCoefficients.lean:152-187;
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
Mathlib/RingTheory/LocalRing/Length.lean:105-126 and
Mathlib/RingTheory/Length.lean:129-133. The length, Tor and generic-point
comparisons keep their mathematical owners in the three lower imports.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open scoped TensorProduct

universe u
namespace Stacks.Chow

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
local notation3 (prettyPrint := false) "R'" =>
  correspondenceIncidenceAmbientStalk fX fY fZ z' w'
local notation3 (prettyPrint := false) "R₀" =>
  correspondenceIncidenceAmbientStalk X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "T'" =>
  correspondenceIncidenceAmbientTor fX fY fZ z' w'
local notation3 (prettyPrint := false) "T₀" =>
  correspondenceIncidenceAmbientTor X.hom Y.hom Z.hom z w

/-- At a generic exterior incidence point, every ambient Tor length equals its
original ambient Tor length at the actual image point. -/
theorem nativeExteriorIncidenceTor_length_eq_original
    (x : I') (hx : x ∈ genericPoints I') (n : ℕ) :
    Module.length (R' x) (T' x n) =
      Module.length (R₀ (π x)) (T₀ (π x) n) := by
  let : Algebra ((I₀).presheaf.stalk (π x)) ((I').presheaf.stalk x) :=
    ((π).stalkMap x).hom.toAlgebra
  let := correspondenceIncidenceTorModule X.hom Y.hom Z.hom z w (π x) n
  let := correspondenceIncidenceTorModule fX fY fZ z' w' x n
  calc
    Module.length (R' x) (T' x n) =
        Module.length ((I').presheaf.stalk x) (T' x n) :=
      correspondenceIncidenceTor_length_eq_incidence fX fY fZ z' w' x n
    _ = Module.length ((I').presheaf.stalk x)
        (((I').presheaf.stalk x) ⊗[(I₀).presheaf.stalk (π x)] T₀ (π x) n) :=
      (nativeExteriorIncidenceTorBaseChangeEquiv X Y Z T z w hz hw x n).length_eq
    _ = Module.length ((I₀).presheaf.stalk (π x)) (T₀ (π x) n) :=
      (π).length_baseChange_stalkMap_of_mem_genericPoints x hx (T₀ (π x) n)
    _ = Module.length (R₀ (π x)) (T₀ (π x) n) :=
      (correspondenceIncidenceTor_length_eq_incidence
        X.hom Y.hom Z.hom z w (π x) n).symm

/-- Naming the original generic point transports the entire dependent length
expression along the actual generic-point projection equality. -/
theorem nativeExteriorIncidenceGenericTor_length
    (η : genericPoints I₀) (n : ℕ) :
    Module.length (R' (G η).val) (T' (G η).val n) =
      Module.length (R₀ η.val) (T₀ η.val n) := by
  exact (nativeExteriorIncidenceTor_length_eq_original X Y Z T z w hz hw
    (G η).val (G η).property n).trans
      (congrArg (fun y : I₀ => Module.length (R₀ y) (T₀ y n))
        (nativeExteriorIncidenceGenericsEquiv_original X Y Z T z w hz hw η))

/-- The actual signed integer Tor term is unchanged in every degree, including zero. -/
theorem correspondenceIncidenceTorTerm_nativeExterior
    (η : genericPoints I₀) (n : ℕ) :
    correspondenceIncidenceTorTerm k fX fY fZ z' w' (G η) n =
      correspondenceIncidenceTorTerm k X.hom Y.hom Z.hom z w η n := by
  change (-1 : ℤ) ^ n * ((Module.length (R' (G η).val) (T' (G η).val n)).toNat : ℤ) =
    (-1 : ℤ) ^ n * ((Module.length (R₀ η.val) (T₀ η.val n)).toNat : ℤ)
  exact congrArg (fun l : ℕ∞ => (-1 : ℤ) ^ n * (l.toNat : ℤ))
    (nativeExteriorIncidenceGenericTor_length X Y Z T z w hz hw η n)

/-- The existing finite alternating Tor coefficient agrees under the actual
exterior generic-point equivalence, without comparing ambient dimension bounds. -/
theorem correspondenceIncidenceTorCoefficient_nativeExterior
    (η : genericPoints I₀) :
    correspondenceIncidenceTorCoefficient k fX fY fZ z' w' (G η) =
      correspondenceIncidenceTorCoefficient k X.hom Y.hom Z.hom z w η := by
  unfold correspondenceIncidenceTorCoefficient
  exact finsum_congr fun n =>
    correspondenceIncidenceTorTerm_nativeExterior X Y Z T z w hz hw η n

end Stacks.Chow
