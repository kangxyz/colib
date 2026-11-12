/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Scheme.GlobalSupportedParameterGeometry
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientOpenRestriction
public import Colib.AlgebraicGeometry.Scheme.IntegerBaseCanonicalRow

/-!
# The integral Spec row as a natural isomorphism of actual open pairs

The two original row symmetries give an isomorphism of the original coefficient open pair
with the parameter-first product open pair. Its opposite is natural for every actual
integral coefficient map. No quasi-compactness assumption or replacement support is used.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace AlgebraicGeometry.Scheme.GlobalSupportedParameter
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The original coefficient open pairs and their complete coefficient squares. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedCoefficientGeometry.lean:31"
  "adaptation" "Original supported Spec pair symmetry on native open arrows"]
def coefficientPairs : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ Scheme.OpenPairs.{u}ᵒᵖ where
  obj a := op (boundedAboveFlatCoefficientOpenPair f a)
  map g := (boundedAboveFlatCoefficientOpenPairMap f g).op
  map_id a := by
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Arrow.Hom.ext
    · exact AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_id (op P, a)
    · exact AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_id (op Q, a)
  map_comp g h := by
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Arrow.Hom.ext
    · exact coefficientMap_comp P g h
    · exact coefficientMap_comp Q g h

/-- Both actual row symmetries form the original open-pair square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedCoefficientGeometry.lean:48"
  "adaptation" "Original supported Spec pair symmetry on native open arrows"]
def coefficientPairIso (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    boundedAboveFlatCoefficientOpenPair f a ≅ pair f.left (Spec a.right) :=
  MorphismProperty.Arrow.isoMk (canonicalRowIso P a) (canonicalRowIso Q a)
      (canonicalRowIso_scheme f a).symm

/-- The open corner is exactly the prescribed row symmetry. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedCoefficientGeometry.lean:55"
  "adaptation" "Original supported Spec pair symmetry on native open arrows"]
theorem coefficientPairIso_hom_left (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (coefficientPairIso f a).hom.left = (canonicalRowIso P a).hom := rfl

/-- The ambient corner is exactly the prescribed row symmetry. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedCoefficientGeometry.lean:59"
  "adaptation" "Original supported Spec pair symmetry on native open arrows"]
theorem coefficientPairIso_hom_right (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (coefficientPairIso f a).hom.right = (canonicalRowIso Q a).hom := rfl

/-- Opposite row symmetry goes from parameter support to original coefficient support. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedCoefficientGeometry.lean:63"
  "adaptation" "Original supported Spec pair symmetry on native open arrows"]
def coefficientPairsIso :
    specUnder ⋙ (pairs f.left).op ≅ coefficientPairs f :=
  NatIso.ofComponents (fun a => (coefficientPairIso f a).op) (by
    intro a b g
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Arrow.Hom.ext
    · exact (canonicalRowIso_coefficient P g).symm
    · exact (canonicalRowIso_coefficient Q g).symm)

end AlgebraicGeometry.Scheme.GlobalSupportedParameter

