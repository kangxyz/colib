/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedInputNormalization

/-! # The independent supported tensor action through the original forgetful functor

The supported action is the original full-subcategory lift. Its genuine comparison
with ambient tensor preserves the forward unit automorphism before normalization.
The resulting exact-functor square produces a whole spectrum prism.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual ambient tensor functor is exact by its original left unitor. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedForgetNaturality.l\
    ean:28"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
theorem tensorCoefficientAmbientTensor_exact :
    IsExact (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq
      (boundedAboveFlatPerfectTensorUnit X) :=
  (IsExact.id _ _).of_iso (boundedAboveFlatPerfectTensorUnitIso X).symm

/-- Forgetting the original support commutes with tensor through its genuine underlying iso. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedForgetNaturality.l\
    ean:35"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
def tensorSupportedForgetIso :
    boundedAboveFlatPerfectSupportedTensorUnit j ⋙ tensorCoefficientSupportedForget j ≅
      tensorCoefficientSupportedForget j ⋙ boundedAboveFlatPerfectTensorUnit X :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (by intro A B g; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

/-- The original supported forward unit agrees with the actual ambient tensor coefficient. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedForgetNaturality.l\
    ean:42"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
theorem tensorSupportedForget_unit (r : (Γ(X, ⊤))ˣ) :
    Functor.whiskerRight (boundedAboveFlatPerfectSupportedTensorUnitAutomorphism j r).hom
        (tensorCoefficientSupportedForget j) ≫ (tensorSupportedForgetIso j).hom =
      (tensorSupportedForgetIso j).hom ≫
        Functor.whiskerLeft (tensorCoefficientSupportedForget j)
          (boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom := by
  apply NatTrans.ext
  funext K
  apply (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_injective
  simp only [NatTrans.comp_app, tensorSupportedForgetIso,
    NatIso.ofComponents_hom_app, Iso.refl_hom,
    Category.id_comp, Category.comp_id, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  exact (boundedAboveFlatPerfectSupportedTensorUnitAutomorphism_hom_original j r K).trans
    (boundedAboveFlatPerfectTensorUnitAutomorphism_hom_original X r
      ((tensorCoefficientSupportedForget j).obj K)).symm

/-- Whole normalized spectrum pastings retain the independent supported/ambient tensor square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedForgetNaturality.l\
    ean:59"
  "adaptation" "Original supported pair tensor, forget square and chosen-zero normalization."]
def tensorSupportedForgetPasting (r : (Γ(X, ⊤))ˣ) :=
  exactOriginalPrespectrumPastingHomotopy
    (boundedAboveFlatPerfectSupportedWaldhausen j)
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
    ((boundedAboveFlatPerfectSupportedTensorUnit_exact j).comp
      (tensorCoefficientSupportedForget_exact j))
    ((boundedAboveFlatPerfectSupportedTensorUnit_exact j).comp
      (tensorCoefficientSupportedForget_exact j))
    ((tensorCoefficientSupportedForget_exact j).comp (tensorCoefficientAmbientTensor_exact))
    ((tensorCoefficientSupportedForget_exact j).comp (tensorCoefficientAmbientTensor_exact))
    (Functor.whiskerRight (boundedAboveFlatPerfectSupportedTensorUnitAutomorphism j r).hom
      (tensorCoefficientSupportedForget j))
    (tensorSupportedForgetIso j).hom (tensorSupportedForgetIso j).hom
    (Functor.whiskerLeft (tensorCoefficientSupportedForget j)
      (boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom)
    (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)
    (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)
    (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)
    (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq_iso _ inferInstance)
    (tensorSupportedForget_unit j r)

end AlgebraicGeometry.Scheme.Modules
