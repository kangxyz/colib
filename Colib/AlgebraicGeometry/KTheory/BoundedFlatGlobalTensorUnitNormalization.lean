/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalTensorUnitEvaluation

/-!
# Normalize genuine tensor multiplication by its whole functor unitor

The input is the original tensor functor and its actual structure-module automorphism.
Conjugation uses its entire natural unitor, and original fully faithful global evaluation
then lifts the resulting identity automorphism. No global tensor pseudofunctor is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Functor.IdentityAutomorphism
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

/-- Conjugate genuine tensor multiplication by the whole original tensor unitor. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalTensorUnitNormalization.lean:25"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
def normalizedTensorUnit (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    𝟭 (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory ≅
      𝟭 (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  (boundedAboveFlatPerfectTensorUnitIso X).symm ≪≫
    boundedAboveFlatPerfectTensorUnitAutomorphism X r ≪≫ boundedAboveFlatPerfectTensorUnitIso X

/-- The entire normalized tensor automorphism equals the original forward scalar. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalTensorUnitNormalization.lean:31"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
theorem normalizedTensorUnit_eq (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    normalizedTensorUnit X r = boundedAboveFlatPerfectGlobalUnitIso X r := by
  apply Iso.ext
  change (boundedAboveFlatPerfectTensorUnitIso X).inv ≫
      (boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom ≫
        (boundedAboveFlatPerfectTensorUnitIso X).hom = _
  rw [boundedAboveFlatPerfectTensorUnitAutomorphism_unitor]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Lift the actual tensor-unitor conjugate through original fully faithful evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalTensorUnitNormalization.lean:41"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
def globalNormalizedTensorUnit (X : Scheme.{u}ᵒᵖ) (r : (Γ(X.unop, ⊤))ˣ) :
    𝟭 (BoundedAboveFlatGlobalSections X) ≅ 𝟭 (BoundedAboveFlatGlobalSections X) :=
  lift (boundedAboveFlatGlobalSectionEvaluation X) (normalizedTensorUnit X.unop r)

/-- The lifted genuine tensor normalization is the existing original global unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalTensorUnitNormalization.lean:46"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
theorem globalNormalizedTensorUnit_eq (X : Scheme.{u}ᵒᵖ) (r : (Γ(X.unop, ⊤))ˣ) :
    globalNormalizedTensorUnit X r = boundedAboveFlatGlobalSectionUnit X r := by
  unfold globalNormalizedTensorUnit
  rw [normalizedTensorUnit_eq]
  rfl

/-- Actual evaluation preserves the whole tensor-unitor normalized automorphism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalTensorUnitNormalization.lean:53"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
theorem globalNormalizedTensorUnit_evaluation (X : Scheme.{u}ᵒᵖ)
    (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (boundedAboveFlatGlobalSectionEvaluation X) (globalNormalizedTensorUnit X r)
      (normalizedTensorUnit X.unop r) :=
  map_lift_hom (boundedAboveFlatGlobalSectionEvaluation X) (normalizedTensorUnit X.unop r)

/-- Every scheme reindexing preserves this same normalized tensor action. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalTensorUnitNormalization.lean:60"
  "adaptation" "Original tensor-unitor normalization and complete supported parameter tracks."]
theorem globalNormalizedTensorUnit_reindex {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y)
    (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (boundedAboveFlatGlobalSectionModelFunctor.map f).hom.toFunctor
      (globalNormalizedTensorUnit X r)
      (globalNormalizedTensorUnit Y (Units.map f.unop.appTop.hom.toMonoidHom r)) := by
  rw [globalNormalizedTensorUnit_eq, globalNormalizedTensorUnit_eq]
  exact boundedAboveFlatGlobalSectionUnit_reindex f r

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
