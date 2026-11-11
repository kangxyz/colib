/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedForgetModel
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedPairModel

/-! # Actual supported geometric comparisons after forgetting support

The original pullback composition and evaluation comparisons retain their original ambient
morphisms under the genuine inclusion of supported full
      subcategories. These formulas concern
natural transformations before normalization or realization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules
open GlobalSupportedSection
variable {A B C : Scheme.OpenPairs.{u}}

/-- Genuine supported pullback and the ambient pullback have the same
      underlying map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedPullbackForgetComparison.lean:28"
  "adaptation" "Original full tensor evaluation rectangle through actual support inclusion."]
theorem boundedAboveFlatPerfectSupportedPullback_forget_map (p : A ⟶ B)
    {K L : (boundedAboveFlatPerfectSupported B.hom).FullSubcategory} (k : K ⟶ L) :
    (tensorCoefficientSupportedForget A.hom).map
        ((boundedAboveFlatPerfectSupportedPullback p).map k) =
      (boundedAboveFlatPerfectPullback p.right).map
        ((tensorCoefficientSupportedForget B.hom).map k) := rfl

/-- The actual supported composition edge has the original ambient
      forward component. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedPullbackForgetComparison.lean:36"
  "adaptation" "Original full tensor evaluation rectangle through actual support inclusion."]
theorem boundedAboveFlatPerfectSupportedPullbackCompIso_forget_hom_app
    (f : A ⟶ B) (g : B ⟶ C)
    (K : (boundedAboveFlatPerfectSupported C.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.hom).map
        ((boundedAboveFlatPerfectSupportedPullbackCompIso f g).hom.app K) =
      (boundedAboveFlatPerfectPullbackCompIso f.right g.right).hom.app
        ((tensorCoefficientSupportedForget C.hom).obj K) := by
  apply (boundedAboveFlatPerfectComplex A.right.toRingedSpace).ι.map_injective
  change (boundedAboveFlatPerfectSupported A.hom).ι.map
      ((boundedAboveFlatPerfectSupportedPullbackCompIso f g).hom.app K) = _
  simp only [boundedAboveFlatPerfectSupportedPullbackCompIso,
      boundedAboveFlatPerfectPullbackCompIso,
    fullyFaithfulCancelRight_hom_app, isoWhiskerLeft_hom, whiskerLeft_app,
    Functor.map_preimage]
  rfl

/-- The inverse actual supported composition edge retains the
      original ambient inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedPullbackForgetComparison.lean:52"
  "adaptation" "Original full tensor evaluation rectangle through actual support inclusion."]
theorem boundedAboveFlatPerfectSupportedPullbackCompIso_forget_inv_app
    (f : A ⟶ B) (g : B ⟶ C)
    (K : (boundedAboveFlatPerfectSupported C.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.hom).map
        ((boundedAboveFlatPerfectSupportedPullbackCompIso f g).inv.app K) =
      (boundedAboveFlatPerfectPullbackCompIso f.right g.right).inv.app
        ((tensorCoefficientSupportedForget C.hom).obj K) := by
  apply (boundedAboveFlatPerfectComplex A.right.toRingedSpace).ι.map_injective
  change (boundedAboveFlatPerfectSupported A.hom).ι.map
      ((boundedAboveFlatPerfectSupportedPullbackCompIso f g).inv.app K) = _
  simp only [boundedAboveFlatPerfectSupportedPullbackCompIso,
      boundedAboveFlatPerfectPullbackCompIso,
    fullyFaithfulCancelRight_inv_app, isoWhiskerLeft_inv, whiskerLeft_app,
    Functor.map_preimage]
  rfl

namespace GlobalSectionChangeIndex
attribute [local irreducible] boundedAboveFlatGlobalSectionEvaluation

/-- The original evaluated component is unchanged by forgetting support. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedPullbackForgetComparison.lean:71"
  "adaptation" "Original full tensor evaluation rectangle through actual support inclusion."]
theorem supportedPairReindexEvaluationIso_forget_hom_app (p : A ⟶ B)
    (K : (boundedAboveFlatGlobalSectionSupported (X := Opposite.op B.right)
      B.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.hom).map
        ((boundedAboveFlatGlobalSupportedPairReindexEvaluationIso p).hom.app K) =
      (boundedAboveFlatGlobalEvaluationPullbackIso p.right).hom.app K.obj := by
  apply (boundedAboveFlatPerfectComplex A.right.toRingedSpace).ι.map_injective
  change (boundedAboveFlatPerfectSupported A.hom).ι.map
      ((boundedAboveFlatGlobalSupportedPairReindexEvaluationIso p).hom.app K) = _
  simp only [boundedAboveFlatGlobalSupportedPairReindexEvaluationIso,
      fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, ObjectProperty.ι_obj]

end GlobalSectionChangeIndex

end AlgebraicGeometry.Scheme.Modules
