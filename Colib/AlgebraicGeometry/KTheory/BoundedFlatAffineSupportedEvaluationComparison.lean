/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSupportedSectionWaldhausen
public import Colib.KTheory.Waldhausen.Iterated.ExactModelEquivalence

/-!
# Actual supported evaluation into the original common-universe model

The genuine supported evaluation equivalence followed by the existing universe-lifting
equivalence is exact in both directions.
The independently chosen geometric zero requires canonical zero normalization. The explicit
normalization iso transports the genuine equivalence and gives a chosen-zero Model map; no equality
between independent zeros is assumed. Coefficient naturality remains separate.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineSupportedSectionEquivalence boundedAboveFlatAffineSupportedEvaluation


/-- The original supported section category is small in universe `u + 1`. -/
def boundedAboveFlatAffineSupportedSectionModel :
    WideSubcategory preservesZero.{u + 1} :=
  ⟨{ Obj := BoundedAboveFlatAffineSupportedSections j,
     waldhausen := boundedAboveFlatAffineSupportedSectionWaldhausen j }⟩

/-- The proved original supported equivalence followed by the actual common-universe equivalence.
-/
def boundedAboveFlatAffineSupportedSectionSmallEquivalence :
    BoundedAboveFlatAffineSupportedSections j ≌
      AsSmall.{0} (boundedAboveFlatPerfectSupported j).FullSubcategory :=
  (boundedAboveFlatAffineSupportedSectionEquivalence j).trans AsSmall.equiv

/-- Forward evaluation into the existing original small model is exact. -/
theorem boundedAboveFlatAffineSupportedSectionSmallEquivalence_exact :
    IsExact (boundedAboveFlatAffineSupportedSectionWaldhausen j).cof
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).weq
      (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.weq
      (boundedAboveFlatAffineSupportedSectionSmallEquivalence j).functor := by
  change IsExact _ _ _ _ ((boundedAboveFlatAffineSupportedSectionEquivalence j).functor ⋙
    AsSmall.up)
  rw [boundedAboveFlatAffineSupportedSectionEquivalence_functor]
  exact (boundedAboveFlatAffineSupportedEvaluation_exact j).comp
    (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall_up_exact

/-- The original inverse equivalence followed by universe lowering is exact as well. -/
theorem boundedAboveFlatAffineSupportedSectionSmallEquivalence_inverse_exact :
    IsExact (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.weq
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).cof
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).weq
      (boundedAboveFlatAffineSupportedSectionSmallEquivalence j).inverse :=
  (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall_down_exact.comp
    (boundedAboveFlatAffineSupportedSectionEquivalence_inverse_exact j)

/-- The actual normalization iso from unchanged evaluation and original universe lifting. -/
def boundedAboveFlatAffineSupportedSectionEvaluationNormalizationIso :
    (boundedAboveFlatAffineSupportedSectionSmallEquivalence j).functor ≅
      CategoryTheory.rebaseFunctor (boundedAboveFlatAffineSupportedSectionSmallEquivalence
        j).functor
        (boundedAboveFlatAffineSupportedSectionWaldhausen j).zero
        (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.zero
        (((boundedAboveFlatAffineSupportedSectionSmallEquivalence_exact j).zero
          (boundedAboveFlatAffineSupportedSectionWaldhausen j).isZero).iso
          (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.isZero) :=
  CategoryTheory.rebaseFunctorIso _ _ _ _

/-- The genuine original equivalence transported through precisely its zero normalization. -/
def boundedAboveFlatAffineSupportedSectionNormalizedEquivalence :
    BoundedAboveFlatAffineSupportedSections j ≌
      AsSmall.{0} (boundedAboveFlatPerfectSupported j).FullSubcategory :=
  (boundedAboveFlatAffineSupportedSectionSmallEquivalence j).changeFunctor
    (boundedAboveFlatAffineSupportedSectionEvaluationNormalizationIso j)

/-- The canonically normalized original evaluation remains exact. -/
theorem boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_exact :
    IsExact (boundedAboveFlatAffineSupportedSectionWaldhausen j).cof
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).weq
      (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.weq
      (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence j).functor :=
  (boundedAboveFlatAffineSupportedSectionSmallEquivalence_exact j).rebase

/-- Changing the forward functor retains the original exact inverse literally. -/
theorem boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_inverse_exact :
    IsExact (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.weq
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).cof
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).weq
      (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence j).inverse :=
  boundedAboveFlatAffineSupportedSectionSmallEquivalence_inverse_exact j

/-- Canonically zero-normalized evaluation gives a map into the original supported model. -/
def boundedAboveFlatAffineSupportedSectionEvaluationModelMap :
    boundedAboveFlatAffineSupportedSectionModel j ⟶
      asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen j) :=
  ⟨⟨(boundedAboveFlatAffineSupportedSectionNormalizedEquivalence j).functor,
    boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_exact j⟩,
    CategoryTheory.rebaseFunctor_obj_base _ _ _ _⟩

/-- The specified normalization, rather than an equality of independently chosen zeros,
identifies the original evaluation functor with the actual Model arrow. -/
def boundedAboveFlatAffineSupportedSectionEvaluationModelIso :
    boundedAboveFlatAffineSupportedEvaluation j ⋙ AsSmall.up ≅
      (boundedAboveFlatAffineSupportedSectionEvaluationModelMap j).hom.toFunctor := by
  refine ?_ ≪≫ boundedAboveFlatAffineSupportedSectionEvaluationNormalizationIso j
  change boundedAboveFlatAffineSupportedEvaluation j ⋙ AsSmall.up ≅
    (boundedAboveFlatAffineSupportedSectionEquivalence j).functor ⋙ AsSmall.up
  rw [boundedAboveFlatAffineSupportedSectionEquivalence_functor]

/-- The actual iterated-S map of the specified normalized evaluation Model arrow. -/
def boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap :
    prespectrum (boundedAboveFlatAffineSupportedSectionModel j) ⟶
      originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen j) :=
  prespectrumMap (boundedAboveFlatAffineSupportedSectionEvaluationModelMap j)

/-- The normalized forward equivalence carries the original chosen zero to the target zero. -/
theorem boundedAboveFlatAffineSupportedSectionNormalizedEquivalence_zero :
    (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence j).functor.obj
        (boundedAboveFlatAffineSupportedSectionWaldhausen j).zero =
      (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.zero :=
  CategoryTheory.rebaseFunctor_obj_base _ _ _ _

end AlgebraicGeometry.Scheme.Modules
