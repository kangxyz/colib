/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.Complements
public import Colib.CategoryTheory.Abelian.ZeroPushout
public import Colib.CategoryTheory.Waldhausen.Cofinality.DenseSubcategory

/-!
# Constructed native dense cofiber data for the honest open-derived image

The original perfect cofibration pushout maps to an actual ambient pushout. Its actual zero
vertex produces a short exact sequence on the original injection and quotient, so the proved
image extension and quotient closure apply without replacing its cofiber. Actual perfect
complements provide density. Only the two explicitly stated geometric inputs remain.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/Dense.lean:42-73`
and `GlobalDense.lean:45-55` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d} U.Modules]

local notation "W" => RingedSpace.perfectComplexesWaldhausen U.toRingedSpace
local notation "P" => RingedSpace.IsPerfectComplex (X := U.toRingedSpace)

/-- The chosen native perfect zero lies in the honest derived restriction image. -/
theorem zero_mem : objects j (W).zero :=
  (complexObjects j).prop_of_isZero
    ((CofibrationClosedSubcategory.inclusion_exact (complexes U.Modules) P
      (RingedSpace.perfectComplexes_cofibrationClosed U.toRingedSpace)).zero (W).isZero)

/-- The original cofiber pushout gives extension membership by its actual short exact sequence. -/
theorem extension_mem (hroof : HasDerivedRoofs j)
    {A B Q : ObjectProperty.FullSubcategory P} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : (W).cof i)
    (h : IsPushout i ((W).isZero.from_ A) q ((W).isZero.to_ Q))
    (hA : objects j A) (hQ : objects j Q) : objects j B := by
  have hp := (CofibrationClosedSubcategory.inclusion_exact (complexes U.Modules) P
    (RingedSpace.perfectComplexes_cofibrationClosed U.toRingedSpace)).pushout hi h
  have : Mono ((ObjectProperty.ι P).map i) := hi
  obtain ⟨z, hz⟩ := Abelian.shortExact_of_mono_pushout_zero
    ((CofibrationClosedSubcategory.inclusion_exact (complexes U.Modules) P
      (RingedSpace.perfectComplexes_cofibrationClosed U.toRingedSpace)).zero (W).isZero) hp
  exact complexObjects_of_shortExact j hroof hz hA hQ

/-- Quotient closure retains the actual chosen cofiber and original quotient arrow. -/
theorem quotient_mem (hroof : HasDerivedRoofs j)
    {A B Q : ObjectProperty.FullSubcategory P} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : (W).cof i)
    (h : IsPushout i ((W).isZero.from_ A) q ((W).isZero.to_ Q))
    (hA : objects j A) (hB : objects j B) : objects j Q := by
  have hp := (CofibrationClosedSubcategory.inclusion_exact (complexes U.Modules) P
    (RingedSpace.perfectComplexes_cofibrationClosed U.toRingedSpace)).pushout hi h
  have : Mono ((ObjectProperty.ι P).map i) := hi
  obtain ⟨z, hz⟩ := Abelian.shortExact_of_mono_pushout_zero
    ((CofibrationClosedSubcategory.inclusion_exact (complexes U.Modules) P
      (RingedSpace.perfectComplexes_cofibrationClosed U.toRingedSpace)).zero (W).isZero) hp
  exact complexObjects_quotient_of_shortExact j hroof hz hA hB

/-- Actual native roofs and actual native perfect complements construct every density field.
No density, approximation, joint-cylinder or K-equivalence conclusion is assumed. -/
theorem denseCofiberData (hroof : HasDerivedRoofs j) (hc : HasPerfectComplements j) :
    Cofinality.DenseCofiberData (W) (objects j) where
  zero := zero_mem j
  weak f hf := by
    have : QuasiIso f.hom := hf
    exact complexObjects_iff_of_quasiIso j f.hom
  extension := extension_mem j hroof
  quotient := quotient_mem j hroof
  complement := coprod_complement j hc

end AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

attribute [colib_tag "COL-0315",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/Dense.lean:42-73"
    "adaptation"
    "Original zero pushout to actual short exact sequence; native roofs \
    and actual complements remain explicit"]
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.extension_mem
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.quotient_mem
  AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.denseCofiberData
