/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedEvaluationSpectrum

/-! Full-signature consumers for the actual fixed-open supported evaluation. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory Topology
open scoped unitInterval
universe u
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineSupportedSectionEquivalence boundedAboveFlatAffineSupportedEvaluation
  boundedAboveFlatAffineSectionZero

example : boundedAboveFlatAffineSupportedEvaluation j ⋙ AsSmall.up ≅
    (boundedAboveFlatAffineSupportedSectionEvaluationModelMap j).hom.toFunctor :=
  boundedAboveFlatAffineSupportedSectionEvaluationModelIso j

example : (boundedAboveFlatAffineSupportedSectionEvaluationModelMap j).hom.toFunctor.obj
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).zero =
        (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.zero :=
  (boundedAboveFlatAffineSupportedSectionEvaluationModelMap j).property

example : boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap j =
    prespectrumMap (boundedAboveFlatAffineSupportedSectionEvaluationModelMap j) := rfl

example : boundedAboveFlatAffineSupportedSectionEvaluationInversePrespectrumMap j =
    prespectrumMap (boundedAboveFlatAffineSupportedSectionEvaluationInverseModelMap j) := rfl

example : (boundedAboveFlatAffineSupportedSectionNormalizedEquivalence j).inverse =
    (boundedAboveFlatAffineSupportedSectionSmallEquivalence j).inverse := rfl

example : (boundedAboveFlatAffineSupportedSectionEvaluationModelMap j).hom.toFunctor =
    CategoryTheory.rebaseFunctor
      (boundedAboveFlatAffineSupportedSectionSmallEquivalence j).functor
      (boundedAboveFlatAffineSupportedSectionWaldhausen j).zero
      (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.zero
      (((boundedAboveFlatAffineSupportedSectionSmallEquivalence_exact j).zero
        (boundedAboveFlatAffineSupportedSectionWaldhausen j).isZero).iso
        (boundedAboveFlatPerfectSupportedWaldhausen j).asSmall.isZero) := rfl

example : (boundedAboveFlatAffineSupportedSectionSmallEquivalence j).functor =
    boundedAboveFlatAffineSupportedEvaluation j ⋙ AsSmall.up := by
  change (boundedAboveFlatAffineSupportedSectionEquivalence j).functor ⋙ AsSmall.up = _
  rw [boundedAboveFlatAffineSupportedSectionEquivalence_functor]
