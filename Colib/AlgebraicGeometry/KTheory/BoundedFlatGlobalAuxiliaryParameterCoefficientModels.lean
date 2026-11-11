/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Scheme.GlobalAuxiliaryCoefficientPairs
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedPairDiagram
public import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterAuxiliarySupportMaps
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFiberLocalizationModels
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedRestrictionModel


/-!
# Actual auxiliary-supported integral coefficient Model comparisons

Each component first uses the complete parameter support-pair isomorphism and then the
original supported coefficient restriction. The three targets are the original G7 fine
fiber, auxiliary ambient, and supported full-open Models. Their original zero objects are
preserved by the actual Model arrows, without introducing a new coarse family.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection

variable (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (T : Q.left.Opens)

/-- The actual parameter auxiliary-supported Model maps to the original native fine Model. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientModels.lean:36"
  "adaptation" "Original three auxiliary supported Spec Model components and selected zeros"]
def ambientComponent (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterAuxiliarySupport.ambient T).obj (specUnder.obj a) ⟶
      boundedAboveFlatCoefficientSupportedAmbientModel T a :=
  pairSupported.map (parameterSupportPairIso Q T a).hom.op ≫
    supportedRestrictionModel _ (op Q, a) (boundedAboveFlatCoefficientSupportOpen Q T a).ι

/-- The component retains the selected zero of the original native auxiliary Model. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientModels.lean:43"
  "adaptation" "Original three auxiliary supported Spec Model components and selected zeros"]
theorem ambientComponent_zero (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ambientComponent Q T a).hom.toFunctor.obj
        ((ParameterAuxiliarySupport.ambient T).obj (specUnder.obj a)).obj.waldhausen.zero =
      (boundedAboveFlatCoefficientSupportedAmbientModel T a).obj.waldhausen.zero :=
  (ambientComponent Q T a).property

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The union support is exactly the old G7 native fiber Model. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientModels.lean:53"
  "adaptation" "Original three auxiliary supported Spec Model components and selected zeros"]
theorem fiberModel_eq (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    boundedAboveFlatCoefficientSupportedAmbientModel (T ⊔ f.left.opensRange) a =
      boundedAboveFlatCoefficientSupportedFiberModel f T a := by
  exact congrArg (fun U : (space (op Q, a)).Opens =>
    boundedAboveFlatCoefficientSupportedSectionModel (i := (op Q, a)) U.ι)
    (fiberSupportOpen_eq f T a).symm

omit [IsOpenImmersion f.left] in
/-- The inverse-image support is exactly the old G7 native full-open Model. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientModels.lean:62"
  "adaptation" "Original three auxiliary supported Spec Model components and selected zeros"]
theorem openModel_eq (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    boundedAboveFlatCoefficientSupportedAmbientModel (f.left ⁻¹ᵁ T) a =
      boundedAboveFlatCoefficientSupportedFullOpenModel f T a := by
  exact congrArg (fun U : (space (op P, a)).Opens =>
    boundedAboveFlatCoefficientSupportedSectionModel (i := (op P, a)) U.ι)
    (boundedAboveFlatCoefficientOpenSupportOpen_eq f T a).symm

/-- The actual union-support comparison targets the original G7 fiber Model. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientModels.lean:70"
  "adaptation" "Original three auxiliary supported Spec Model components and selected zeros"]
def fiberComponent (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterAuxiliarySupport.fiber f.left T).obj (specUnder.obj a) ⟶
      boundedAboveFlatCoefficientSupportedFiberModel f T a :=
  ambientComponent Q (T ⊔ f.left.opensRange) a ≫ eqToHom (fiberModel_eq f T a)

/-- The actual inverse-image-support comparison targets the original G7 full-open Model. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientModels.lean:76"
  "adaptation" "Original three auxiliary supported Spec Model components and selected zeros"]
def openComponent (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterAuxiliarySupport.openModel f.left T).obj (specUnder.obj a) ⟶
      boundedAboveFlatCoefficientSupportedFullOpenModel f T a :=
  ambientComponent P (f.left ⁻¹ᵁ T) a ≫ eqToHom (openModel_eq f T a)

/-- The actual fiber comparison preserves the old G7 selected zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientModels.lean:82"
  "adaptation" "Original three auxiliary supported Spec Model components and selected zeros"]
theorem fiberComponent_zero (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (fiberComponent f T a).hom.toFunctor.obj
        ((ParameterAuxiliarySupport.fiber f.left T).obj (specUnder.obj a)).obj.waldhausen.zero =
      (boundedAboveFlatCoefficientSupportedFiberModel f T a).obj.waldhausen.zero :=
  (fiberComponent f T a).property

omit [IsOpenImmersion f.left] in
/-- The actual full-open comparison preserves the old G7 selected zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientModels.lean:90"
  "adaptation" "Original three auxiliary supported Spec Model components and selected zeros"]
theorem openComponent_zero (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (openComponent f T a).hom.toFunctor.obj
        ((ParameterAuxiliarySupport.openModel f.left T).obj (specUnder.obj a)).obj.waldhausen.zero =
      (boundedAboveFlatCoefficientSupportedFullOpenModel f T a).obj.waldhausen.zero :=
  (openComponent f T a).property

end AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
