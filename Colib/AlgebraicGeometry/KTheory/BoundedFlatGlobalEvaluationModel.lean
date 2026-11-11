/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalTensorUnitEvaluation
public import Colib.KTheory.Waldhausen.Iterated.Prespectrum
public import Colib.CategoryTheory.Functor.IdentityAutomorphismRebase

/-! # Actual chosen-zero normalization of global evaluation -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Functor.IdentityAutomorphism
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

local instance boundedAboveFlatGlobalSectionEvaluationDownEquivalence (X : Scheme.{u}ᵒᵖ) :
    (AsSmall.down : AsSmall.{0} ((boundedAboveFlatPerfectComplex
      X.unop.toRingedSpace).FullSubcategory) ⥤
      (boundedAboveFlatPerfectComplex X.unop.toRingedSpace).FullSubcategory).IsEquivalence :=
  AsSmall.equiv.symm.isEquivalence_functor

/-- Original evaluation in the fixed common universe. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationModel.lean:27"
  "adaptation" "Original evaluation, chosen-zero normalization and unit transport"]
def evaluationSmall (X : Scheme.{u}ᵒᵖ) :
    (boundedAboveFlatGlobalSectionModelFunctor.obj X).obj.Obj ⥤ AsSmall.{0}
      ((boundedAboveFlatPerfectComplex X.unop.toRingedSpace).FullSubcategory) :=
  boundedAboveFlatGlobalSectionEvaluation X ⋙ AsSmall.up

/-- The unchanged evaluation and common-universe lift are exact. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationModel.lean:32"
  "adaptation" "Original evaluation, chosen-zero normalization and unit transport"]
theorem evaluationSmall_exact (X : Scheme.{u}ᵒᵖ) :
    IsExact (boundedAboveFlatGlobalSectionModelFunctor.obj X).obj.waldhausen.cof
      (boundedAboveFlatGlobalSectionModelFunctor.obj X).obj.waldhausen.weq
      (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).asSmall.cof
      (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).asSmall.weq (evaluationSmall X) :=
  (boundedAboveFlatGlobalSectionEvaluation_exact X).comp (boundedAboveFlatPerfectWaldhausen
      X.unop.toRingedSpace).asSmall_up_exact

/-- The original evaluated zero has its unique comparison with the target chosen zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationModel.lean:39"
  "adaptation" "Original evaluation, chosen-zero normalization and unit transport"]
def evaluationZeroIso (X : Scheme.{u}ᵒᵖ) :
    (evaluationSmall X).obj (boundedAboveFlatGlobalSectionModelFunctor.obj X).obj.waldhausen.zero ≅
      (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).asSmall.zero :=
  ((evaluationSmall_exact X).zero (boundedAboveFlatGlobalSectionModelFunctor.obj
      X).obj.waldhausen.isZero).iso
    (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).asSmall.isZero

/-- Actual evaluation normalized only on its selected zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationModel.lean:46"
  "adaptation" "Original evaluation, chosen-zero normalization and unit transport"]
def evaluationModel (X : Scheme.{u}ᵒᵖ) :
    boundedAboveFlatGlobalSectionModelFunctor.obj X ⟶ asSmallCategory
      (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace) :=
  ⟨⟨CategoryTheory.rebaseFunctor (evaluationSmall X)
      (boundedAboveFlatGlobalSectionModelFunctor.obj X).obj.waldhausen.zero
      (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).asSmall.zero
      (evaluationZeroIso X), (evaluationSmall_exact X).rebase⟩,
    CategoryTheory.rebaseFunctor_obj_base _ _ _ _⟩

/-- Retain the original complete normalization isomorphism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationModel.lean:54"
  "adaptation" "Original evaluation, chosen-zero normalization and unit transport"]
def evaluationNormalizationIso (X : Scheme.{u}ᵒᵖ) :
    evaluationSmall X ≅ (evaluationModel X).hom.toFunctor :=
  CategoryTheory.rebaseFunctorIso _ _ _ (evaluationZeroIso X)

/-- The original scalar identity automorphism in the common universe. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationModel.lean:59"
  "adaptation" "Original evaluation, chosen-zero normalization and unit transport"]
def evaluationSmallUnit (X : Scheme.{u}ᵒᵖ) (r : (Γ(X.unop, ⊤))ˣ) :
    𝟭 (AsSmall.{0} ((boundedAboveFlatPerfectComplex X.unop.toRingedSpace).FullSubcategory)) ≅
      𝟭 (AsSmall.{0} ((boundedAboveFlatPerfectComplex X.unop.toRingedSpace).FullSubcategory)) :=
  lift (AsSmall.down : AsSmall.{0} ((boundedAboveFlatPerfectComplex
      X.unop.toRingedSpace).FullSubcategory) ⥤ (boundedAboveFlatPerfectComplex
      X.unop.toRingedSpace).FullSubcategory)
    (boundedAboveFlatPerfectGlobalUnitIso X.unop r)

/-- Universe lifting retains the evaluated original forward scalar. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationModel.lean:66"
  "adaptation" "Original evaluation, chosen-zero normalization and unit transport"]
theorem evaluationSmall_unit (X : Scheme.{u}ᵒᵖ) (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (evaluationSmall X) (boundedAboveFlatGlobalSectionUnit X r) (evaluationSmallUnit X
      r) := by
  intro S
  apply (AsSmall.down : AsSmall.{0} ((boundedAboveFlatPerfectComplex
      X.unop.toRingedSpace).FullSubcategory) ⥤
    (boundedAboveFlatPerfectComplex X.unop.toRingedSpace).FullSubcategory).map_injective
  change (boundedAboveFlatGlobalSectionEvaluation X).map ((boundedAboveFlatGlobalSectionUnit X
      r).hom.app S) =
    AsSmall.down.map ((evaluationSmallUnit X r).hom.app
      (AsSmall.up.obj ((boundedAboveFlatGlobalSectionEvaluation X).obj S)))
  rw [evaluationSmallUnit, map_lift_hom]
  exact boundedAboveFlatGlobalSectionUnit_evaluation X r S

/-- Actual zero normalization preserves the same original unit, without a new choice. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationModel.lean:78"
  "adaptation" "Original evaluation, chosen-zero normalization and unit transport"]
theorem evaluationModel_unit (X : Scheme.{u}ᵒᵖ) (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (evaluationModel X).hom.toFunctor (boundedAboveFlatGlobalSectionUnit X r)
      (evaluationSmallUnit X r) :=
  rebase_preserves _ _ _ _ _ _ (evaluationSmall_unit X r)

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

attribute [colib_tag "COL-0547"] evaluationModel

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
