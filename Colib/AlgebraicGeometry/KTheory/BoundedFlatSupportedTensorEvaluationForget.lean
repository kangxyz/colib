/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedTensorUnitorForget
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalTensorUnitEvaluation

/-! # Original supported tensor evaluation through the actual support
      inclusion

Every component of the original supported tensor evaluation
      comparison retains both actual
ambient factors. This identity precedes zero normalization and common-universe transport.
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
variable {A B : Scheme.OpenPairs.{u}}

namespace GlobalSectionChangeIndex
attribute [local irreducible] boundedAboveFlatGlobalSectionEvaluation

/-- The actual supported evaluation retains the same underlying
      bounded-flat object. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedEvaluationForget.l\
    ean:30"
  "adaptation" "Original full tensor evaluation rectangle through actual support inclusion."]
theorem supportedEvaluation_forget_obj {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}}
    (j : U ⟶ X.unop) [IsOpenImmersion j] (K : (boundedAboveFlatGlobalSectionSupported
      j).FullSubcategory) :
    (tensorCoefficientSupportedForget j).obj ((boundedAboveFlatGlobalSupportedEvaluation j).obj K) =
      (boundedAboveFlatGlobalSectionEvaluation X).obj K.obj :=
  congrArg (fun F => F.obj K) (boundedAboveFlatGlobalSupportedEvaluation_forget j)

/-- The supported tensor evaluation comparison retains both original
      ambient factors. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedEvaluationForget.l\
    ean:37"
  "adaptation" "Original full tensor evaluation rectangle through actual support inclusion."]
theorem tensorEvaluationIso_forget_hom_app (p : A ⟶ B)
    (K : (boundedAboveFlatGlobalSectionSupported (X := Opposite.op B.right)
      B.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.hom).map
        ((SupportedTensorEvaluation.tensorEvaluationIso p).hom.app K) =
      (tensorEvaluationIso p.right).hom.app K.obj := by
  simp only [SupportedTensorEvaluation.tensorEvaluationIso, tensorEvaluationIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, isoWhiskerLeft_hom,
    whiskerLeft_app, SupportedTensorEvaluation.tensorPairUnitor_forget_hom_app,
    supportedPairReindexEvaluationIso_forget_hom_app]
  rfl

end GlobalSectionChangeIndex

end AlgebraicGeometry.Scheme.Modules
