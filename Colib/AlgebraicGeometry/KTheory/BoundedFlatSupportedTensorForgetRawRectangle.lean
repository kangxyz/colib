/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedTensorEvaluationForget
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedEvaluationForgetModel

/-! # The actual tensor and support-forgetting evaluation rectangle

The two routes use the original supported and ambient tensor
      evaluation transitions and the
actual full-subcategory inclusion. Their complete raw rectangle commutes by the original
underlying transformation equality, before any selected-zero normalization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
open GlobalSupportedSection
open GlobalSectionChangeIndex
attribute [local irreducible] boundedAboveFlatGlobalSectionEvaluation

variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)

/-- The genuine supported section pullback/forgetting square is
      strict before evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetRawRectangle.lean:32"
  "adaptation" "Original full tensor evaluation rectangle through actual support inclusion."]
theorem forgetReindexInputSquare :
    (boundedAboveFlatGlobalSupportedPairModelMap p).hom.toFunctor ⋙
      (boundedAboveFlatGlobalSupportedForget (X := op A.right) A.hom).hom.toFunctor =
      (boundedAboveFlatGlobalSupportedForget (X := op B.right) B.hom).hom.toFunctor ⋙
        (boundedAboveFlatGlobalSectionModelFunctor.map p.right.op).hom.toFunctor :=
  boundedAboveFlatGlobalSupportedPairReindex_forget p

/-- Both complete raw tensor evaluation routes preserve the actual support-forgetting square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedTensorForgetRawRectangle.lean:39"
  "adaptation" "Original full tensor evaluation rectangle through actual support inclusion."]
theorem tensorForgetRawRectangle_hom :
    whiskerLeft (boundedAboveFlatGlobalSupportedEvaluation (X := op B.right) B.hom)
        (tensorSupportedPairForgetIso p).hom ≫
        (isoSquareRoute (evaluationForgetIso (X := op B.right) B.hom)
          (GlobalSectionChangeIndex.tensorEvaluationIso p.right).symm).inv =
      (isoSquareRoute (tensorEvaluationIso p).symm
        (evaluationForgetIso (X := op A.right) A.hom)).inv ≫
        eqToHom (congrArg (fun F => F ⋙ boundedAboveFlatGlobalSectionEvaluation (op A.right))
          (forgetReindexInputSquare p)) := by
  apply NatTrans.ext
  funext K
  change (boundedAboveFlatGlobalSectionSupported (X := op B.right) B.hom).FullSubcategory
      at K
  simp only [isoSquareRoute, Iso.trans_inv, Iso.symm_inv,
    isoWhiskerLeft_inv, isoWhiskerRight_inv, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Functor.associator_inv_app,
    Functor.associator_hom_app,
    tensorSupportedPairForgetIso, evaluationForgetIso, boundedAboveFlatGlobalSupportedForget,
      NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app, Iso.refl_hom, Iso.refl_inv,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  change (boundedAboveFlatPerfectTensorUnitPullback p.right).map
      (𝟙 ((boundedAboveFlatGlobalSectionEvaluation (op B.right)).obj K.obj)) ≫
        (GlobalSectionChangeIndex.tensorEvaluationIso p.right).hom.app K.obj =
    (tensorCoefficientSupportedForget A.hom).map
        ((tensorEvaluationIso p).hom.app K) ≫
      𝟙 ((boundedAboveFlatGlobalSectionEvaluation (op A.right)).obj
        ((boundedAboveFlatGlobalSectionModelFunctor.map p.right.op).hom.toFunctor.obj K.obj))
  calc
    _ = (GlobalSectionChangeIndex.tensorEvaluationIso p.right).hom.app K.obj :=
      (congrArg (fun k => k ≫
        (GlobalSectionChangeIndex.tensorEvaluationIso p.right).hom.app K.obj)
        ((boundedAboveFlatPerfectTensorUnitPullback p.right).map_id _)).trans
          (Category.id_comp _)
    _ = _ := (GlobalSectionChangeIndex.tensorEvaluationIso_forget_hom_app p K).symm.trans
      (Category.comp_id _).symm

end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
