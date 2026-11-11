/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectTensorUnitPullback
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedPairReindex
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSectionUnit

/-!
# Genuine tensor-unit transport through global evaluation

The original tensor unitor and section evaluation transition give the actual comparison.
Its automorphism square keeps the same scalar and the original section unit.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

attribute [local irreducible] boundedAboveFlatGlobalSectionEvaluation
      boundedAboveFlatPerfectGlobalUnitIso

/-- Tensor pullback followed by its actual unitor and original evaluation transition. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalTensorUnitEvaluation.lean:27"
  "adaptation" "Original evaluation, chosen-zero normalization and unit transport"]
def tensorEvaluationIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedAboveFlatGlobalSectionEvaluation (Opposite.op Y) ⋙
      boundedAboveFlatPerfectTensorUnitPullback f ≅
      (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor ⋙
      boundedAboveFlatGlobalSectionEvaluation (Opposite.op X) :=
  Functor.isoWhiskerLeft _ (boundedAboveFlatPerfectTensorUnitPullbackIso f) ≪≫
    boundedAboveFlatGlobalEvaluationPullbackIso f

/-- The genuine tensor automorphism transports to the original evaluated global unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalTensorUnitEvaluation.lean:34"
  "adaptation" "Original evaluation, chosen-zero normalization and unit transport"]
theorem tensorEvaluation_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    Functor.whiskerLeft (boundedAboveFlatGlobalSectionEvaluation (Opposite.op Y))
        (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom ≫
      (tensorEvaluationIso f).hom =
    (tensorEvaluationIso f).hom ≫
      Functor.whiskerRight
        (Functor.whiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor
          (boundedAboveFlatGlobalSectionUnit (Opposite.op X) r).hom)
      (boundedAboveFlatGlobalSectionEvaluation (Opposite.op X)) := by
  apply NatTrans.ext
  funext S
  change (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom.app _ ≫
      ((boundedAboveFlatPerfectTensorUnitPullbackIso f).hom.app _ ≫
        (boundedAboveFlatGlobalEvaluationPullbackIso f).hom.app S) =
    ((boundedAboveFlatPerfectTensorUnitPullbackIso f).hom.app _ ≫
        (boundedAboveFlatGlobalEvaluationPullbackIso f).hom.app S) ≫ _
  have hu := NatTrans.congr_app
    (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism_unitor f r)
    ((boundedAboveFlatGlobalSectionEvaluation (Opposite.op Y)).obj S)
  simp only [NatTrans.comp_app] at hu
  rw [← Category.assoc, hu]
  simp only [Category.assoc, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  have he := boundedAboveFlatGlobalSectionUnit_evaluation (Opposite.op X) r
    ((boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor.obj S)
  rw [he]
  congr 1
  simpa only [boundedAboveFlatGlobalSectionModelFunctor_map_toFunctor,
    boundedAboveFlatPerfectPullbackUnitIso, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.id_map, Functor.id_obj, Functor.comp_obj, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.rightUnitor_hom_app, Category.id_comp, Category.comp_id] using
    ((boundedAboveFlatPerfectGlobalUnitIso X r).hom.naturality
      ((boundedAboveFlatGlobalEvaluationPullbackIso f).hom.app S)).symm

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

attribute [colib_tag "COL-0547"] tensorEvaluation_unit

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
