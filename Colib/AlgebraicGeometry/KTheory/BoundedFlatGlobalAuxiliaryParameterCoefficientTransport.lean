/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterCoefficientRows


/-! # Original native support transport and the complete underlying comparison functors -/
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
open CategoryTheory.Waldhausen.SmallWaldhausenCategory

/-- Equality of actual native support opens transports Models without changing sections. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientTransport.lean:24"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
theorem nativeSupportTransport_forget {R : CommRingCat.{u}} (c : Index R)
    {A B : (space c).Opens} (h : A = B) :
    (eqToHom (congrArg (fun U : (space c).Opens =>
      boundedAboveFlatCoefficientSupportedSectionModel (i := c) U.ι) h)).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported B.ι).ι =
      (boundedAboveFlatCoefficientSectionSupported A.ι).ι := by
  cases h
  rfl

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The full fiber component retains the original ambient section comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientTransport.lean:37"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
theorem fiberComponent_forget (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (fiberComponent f T a).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported
          (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι).ι =
      ((ParameterModels.forget (T ⊔ f.left.opensRange).ι).app (specUnder.obj a)).hom.toFunctor ⋙
        ((parameterCoefficientRestriction Q).app a).hom.toFunctor := by
  have ht := nativeSupportTransport_forget (op Q, a) (fiberSupportOpen_eq f T a).symm
  change (eqToHom (fiberModel_eq f T a)).hom.toFunctor ⋙
      (boundedAboveFlatCoefficientSectionSupported
          (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι).ι =
    (boundedAboveFlatCoefficientSectionSupported
      (boundedAboveFlatCoefficientSupportOpen Q (T ⊔ f.left.opensRange) a).ι).ι at ht
  change (ambientComponent Q (T ⊔ f.left.opensRange) a).hom.toFunctor ⋙
    (eqToHom (fiberModel_eq f T a)).hom.toFunctor ⋙
      (boundedAboveFlatCoefficientSectionSupported
          (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι).ι =
    ((ParameterModels.forget (T ⊔ f.left.opensRange).ι).app (specUnder.obj a)).hom.toFunctor ⋙
      ((parameterCoefficientRestriction Q).app a).hom.toFunctor
  rw [ht, ambientComponent_forget]

omit [IsOpenImmersion f.left] in
/-- The full-open component retains the original ambient section comparison on the open scheme. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientTransport.lean:59"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
theorem openComponent_forget (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (openComponent f T a).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientOpenSupportOpen f
          T a).ι).ι =
      ((ParameterModels.forget (f.left ⁻¹ᵁ T).ι).app (specUnder.obj a)).hom.toFunctor ⋙
        ((parameterCoefficientRestriction P).app a).hom.toFunctor := by
  have ht := nativeSupportTransport_forget (op P, a)
    (boundedAboveFlatCoefficientOpenSupportOpen_eq f T a).symm
  change (eqToHom (openModel_eq f T a)).hom.toFunctor ⋙
      (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientOpenSupportOpen f T
        a).ι).ι =
    (boundedAboveFlatCoefficientSectionSupported
      (boundedAboveFlatCoefficientSupportOpen P (f.left ⁻¹ᵁ T) a).ι).ι at ht
  change (ambientComponent P (f.left ⁻¹ᵁ T) a).hom.toFunctor ⋙
    (eqToHom (openModel_eq f T a)).hom.toFunctor ⋙
      (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientOpenSupportOpen f T
        a).ι).ι =
    ((ParameterModels.forget (f.left ⁻¹ᵁ T).ι).app (specUnder.obj a)).hom.toFunctor ⋙
      ((parameterCoefficientRestriction P).app a).hom.toFunctor
  rw [ht, ambientComponent_forget]

end AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
