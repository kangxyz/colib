/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedEvaluationModel
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationModel
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportHomotopy

/-! # The original supported scalar through actual evaluation and selected-zero transport -/
@[expose] public section
noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
  CategoryTheory.Functor.IdentityAutomorphism
universe u
namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
open GlobalSectionChangeIndex
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
variable {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop) [IsOpenImmersion j]

/-- The same global scalar restricted to actual supported sections. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedEvaluationUnit.lean:26"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def unit (r : (Γ(X.unop, ⊤))ˣ) :
    𝟭 (boundedAboveFlatGlobalSectionSupported j).FullSubcategory ≅ 𝟭
      (boundedAboveFlatGlobalSectionSupported j).FullSubcategory :=
  lift (boundedAboveFlatGlobalSectionSupported j).ι (boundedAboveFlatGlobalSectionUnit X r)

/-- Actual evaluation preserves the original supported scalar componentwise. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedEvaluationUnit.lean:31"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem evaluation_unit (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (boundedAboveFlatGlobalSupportedEvaluation j) (unit j r)
      (boundedAboveFlatPerfectSupportedGlobalUnitIso j r) := by
  intro K
  apply (boundedAboveFlatPerfectSupported j).ι.map_injective
  change (boundedAboveFlatPerfectComplex X.unop.toRingedSpace).ι.map
      ((boundedAboveFlatGlobalSectionEvaluation X).map
        ((boundedAboveFlatGlobalSectionSupported j).ι.map ((unit j r).hom.app K))) = _
  rw [unit, map_lift_hom, boundedAboveFlatGlobalSectionUnit_evaluation]
  simp only [boundedAboveFlatPerfectSupportedGlobalUnitIso, boundedAboveFlatPerfectGlobalUnitIso,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, ObjectProperty.ι_obj]
  rfl

local instance :
    (AsSmall.down : AsSmall.{0} ((boundedAboveFlatPerfectSupported j).FullSubcategory) ⥤
      (boundedAboveFlatPerfectSupported j).FullSubcategory).IsEquivalence :=
  AsSmall.equiv.symm.isEquivalence_functor

/-- The original supported scalar in the fixed common universe. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedEvaluationUnit.lean:50"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def smallUnit (r : (Γ(X.unop, ⊤))ˣ) :
    𝟭 (AsSmall.{0} ((boundedAboveFlatPerfectSupported j).FullSubcategory)) ≅
      𝟭 (AsSmall.{0} ((boundedAboveFlatPerfectSupported j).FullSubcategory)) :=
  lift (AsSmall.down : AsSmall.{0} ((boundedAboveFlatPerfectSupported j).FullSubcategory) ⥤
    (boundedAboveFlatPerfectSupported j).FullSubcategory)
    (boundedAboveFlatPerfectSupportedGlobalUnitIso j r)

/-- Universe transport retains the entire evaluated scalar. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedEvaluationUnit.lean:58"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem evaluationSmall_unit (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (evaluationSmall j) (unit j r) (smallUnit j r) := by
  intro K
  apply (AsSmall.down : AsSmall.{0} ((boundedAboveFlatPerfectSupported j).FullSubcategory) ⥤
    (boundedAboveFlatPerfectSupported j).FullSubcategory).map_injective
  change (boundedAboveFlatGlobalSupportedEvaluation j).map ((unit j r).hom.app K) =
    AsSmall.down.map ((smallUnit j r).hom.app
      (AsSmall.up.obj ((boundedAboveFlatGlobalSupportedEvaluation j).obj K)))
  rw [smallUnit, map_lift_hom]
  exact evaluation_unit j r K

/-- Actual chosen-zero normalization preserves this same supported unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedEvaluationUnit.lean:70"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem evaluationModel_unit (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (evaluationModel j).hom.toFunctor (unit j r) (smallUnit j r) :=
  rebase_preserves _ _ _ _ _ _ (evaluationSmall_unit j r)

end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
