/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedPullbackForgetComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedTensorModelComparison

/-! # The original supported tensor unitor after forgetting support

The actual tensor unitor on a supported pulled-back object retains
      its original ambient
component in both directions through the full-subcategory inclusion.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
open GlobalSupportedSection
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)

/-- The genuine supported tensor unitor retains its original ambient
      forward component. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedUnitorForget.lean:28"
  "adaptation" "Original full tensor evaluation rectangle through actual support inclusion."]
theorem tensorPairUnitor_forget_hom_app
    (K : (boundedAboveFlatPerfectSupported B.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.hom).map ((tensorPairUnitor p).hom.app K) =
      (boundedAboveFlatPerfectTensorUnitPullbackIso p.right).hom.app
        ((tensorCoefficientSupportedForget B.hom).obj K) := by
  apply (boundedAboveFlatPerfectComplex A.right.toRingedSpace).ι.map_injective
  change (boundedAboveFlatPerfectSupported A.hom).ι.map
      ((tensorPairUnitor p).hom.app K) = _
  simp only [tensorPairUnitor, isoWhiskerLeft_hom, whiskerLeft_app,
    boundedAboveFlatPerfectTensorUnitPullbackIso_hom_app,
    boundedAboveFlatPerfectSupportedTensorUnitIso, fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage, boundedAboveFlatPerfectTensorUnitIso_hom_original]
  rfl

/-- The whole actual tensor unitor is retained under support-forgetting. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedUnitorForget.lean:43"
  "adaptation" "Original full tensor evaluation rectangle through actual support inclusion."]
theorem tensorPairUnitor_forget_iso_app
    (K : (boundedAboveFlatPerfectSupported B.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.hom).mapIso ((tensorPairUnitor p).app K) =
      (boundedAboveFlatPerfectTensorUnitPullbackIso p.right).app
        ((tensorCoefficientSupportedForget B.hom).obj K) := by
  apply Iso.ext
  exact tensorPairUnitor_forget_hom_app p K

/-- The genuine supported tensor unitor retains its original ambient
      inverse component. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedUnitorForget.lean:52"
  "adaptation" "Original full tensor evaluation rectangle through actual support inclusion."]
theorem tensorPairUnitor_forget_inv_app
    (K : (boundedAboveFlatPerfectSupported B.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.hom).map ((tensorPairUnitor p).inv.app K) =
      (boundedAboveFlatPerfectTensorUnitPullbackIso p.right).inv.app
        ((tensorCoefficientSupportedForget B.hom).obj K) :=
  congrArg Iso.inv (tensorPairUnitor_forget_iso_app p K)

end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
