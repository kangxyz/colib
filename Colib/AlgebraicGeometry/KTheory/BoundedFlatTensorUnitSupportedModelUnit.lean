/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedTensorModelComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatTensorUnitSupportedEvaluationUnit
public import Colib.CategoryTheory.Functor.IdentityAutomorphismSquare

/-! # The genuine supported tensor coefficient through the complete Model comparison -/
@[expose] public section
noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
  CategoryTheory.Functor.IdentityAutomorphism
universe u
namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
open GlobalSectionChangeIndex
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) (r : (Γ(A.right, ⊤))ˣ)

/-- The actual supported tensor unitor identifies the same objectwise forward scalar. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedModelUnit.lean:26"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem tensorAutomorphism_scalar
    (K : (boundedAboveFlatPerfectSupported B.hom).FullSubcategory) :
    (tensorSupportedPairAutomorphism p r).hom.app K =
      (boundedAboveFlatPerfectSupportedGlobalUnitIso A.hom r).hom.app
        ((tensorSupportedPairFunctor p).obj K) := by
  let L := (boundedAboveFlatPerfectSupportedPullback p).obj K
  apply (cancel_mono ((boundedAboveFlatPerfectSupportedTensorUnitIso A.hom).hom.app L)).mp
  have h := NatTrans.congr_app
    (boundedAboveFlatPerfectSupportedTensorUnitAutomorphism_unitor A.hom r) L
  exact h.trans ((boundedAboveFlatPerfectSupportedGlobalUnitIso A.hom r).hom.naturality
    ((boundedAboveFlatPerfectSupportedTensorUnitIso A.hom).hom.app L))

local instance :
    (AsSmall.down :
      AsSmall.{0} ((boundedAboveFlatPerfectSupported A.hom).FullSubcategory) ⥤
      (boundedAboveFlatPerfectSupported A.hom).FullSubcategory).IsEquivalence :=
  AsSmall.equiv.symm.isEquivalence_functor

/-- The fixed supported zero rebase keeps the original tensor multiplication component. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedModelUnit.lean:45"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem tensorModelTransformation_scalar :
    tensorSupportedPairModelTransformation p r =
      (onFunctor (tensorSupportedPairModelMap p).hom.toFunctor
        (smallUnit (X := op A.right) A.hom r)).hom := by
  apply NatTrans.ext
  funext K
  change AsSmall.{0}
    ((boundedAboveFlatPerfectSupported B.hom).FullSubcategory) at K
  apply (AsSmall.down :
      AsSmall.{0} ((boundedAboveFlatPerfectSupported A.hom).FullSubcategory) ⥤
    (boundedAboveFlatPerfectSupported A.hom).FullSubcategory).map_injective
  rw [onFunctor_hom_app, smallUnit, map_lift_hom]
  simp only [tensorSupportedPairModelTransformation, whiskerLeft_app, whiskerRight_app,
    AsSmall.down_map, AsSmall.up_map_down, normalizedWeakTransformation, NatTrans.comp_app]
  rw [tensorAutomorphism_scalar]
  let z := tensorSupportedPairNormalization p
  have hn := (boundedAboveFlatPerfectSupportedGlobalUnitIso A.hom r).hom.naturality
    (z.hom.app (AsSmall.down.obj K))
  simp only [Functor.id_map, Functor.id_obj] at hn
  change z.inv.app (AsSmall.down.obj K) ≫
      (boundedAboveFlatPerfectSupportedGlobalUnitIso A.hom r).hom.app
        ((tensorSupportedPairFunctor p).obj (AsSmall.down.obj K)) ≫
      z.hom.app (AsSmall.down.obj K) =
    (boundedAboveFlatPerfectSupportedGlobalUnitIso A.hom r).hom.app
      ((tensorSupportedPairNormalizedFunctor p).obj (AsSmall.down.obj K))
  rw [← hn, Iso.inv_hom_id_app_assoc]
  rfl

/-- The full actual supported Model iso intertwines the internal and genuine tensor units. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedModelUnit.lean:74"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem internalTensorModelIso_unit :
    whiskerRight
      (onFunctor
        (GlobalSupportedSection.boundedAboveFlatGlobalSupportedPairModelMap p).hom.toFunctor
        (unit (X := op A.right) A.hom r)).hom
      (evaluationModel (X := op A.right) A.hom).hom.toFunctor ≫
      (internalTensorModelIso p).hom =
    (internalTensorModelIso p).hom ≫
      whiskerLeft (evaluationModel (X := op B.right) B.hom).hom.toFunctor
        (tensorSupportedPairModelTransformation p r) := by
  rw [tensorModelTransformation_scalar]
  exact onFunctor_whisker_square
    (GlobalSupportedSection.boundedAboveFlatGlobalSupportedPairModelMap p).hom.toFunctor
    (tensorSupportedPairModelMap p).hom.toFunctor
    (evaluationModel (X := op B.right) B.hom).hom.toFunctor
    (evaluationModel (X := op A.right) A.hom).hom.toFunctor
    (internalTensorModelIso p).hom
    (unit (X := op A.right) A.hom r)
    (smallUnit (X := op A.right) A.hom r)
    (evaluationModel_unit (X := op A.right) A.hom r).whisker

end AlgebraicGeometry.Scheme.Modules.SupportedTensorEvaluation
