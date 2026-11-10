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

example (n : ℕ) : IsWeakHomotopyEquivalence
    ((boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap j).map n) :=
  boundedAboveFlatAffineSupportedSectionEvaluation_level_isWeakHomotopyEquivalence j n

example : IsWeakHomotopyEquivalence ((boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap
  j).map 0) :=
  boundedAboveFlatAffineSupportedSectionEvaluation_level_isWeakHomotopyEquivalence j 0

example (n : ℕ) : (boundedAboveFlatAffineSupportedSectionEvaluationLevelEquiv j n).toFun =
    (boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap j).map n := rfl

example (n : ℕ) : (boundedAboveFlatAffineSupportedSectionEvaluationLevelEquiv j n).invFun =
    (boundedAboveFlatAffineSupportedSectionEvaluationInversePrespectrumMap j).map n := rfl

example : IsIso
    ((LoopPrespectrum.stableHomotopyFunctor (-1 : ℤ)).map
      (boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap j)) :=
  boundedAboveFlatAffineSupportedSectionEvaluation_isStableEquivalence j (-1)

example : IsIso
    ((LoopPrespectrum.stableHomotopyFunctor (0 : ℤ)).map
      (boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap j)) :=
  boundedAboveFlatAffineSupportedSectionEvaluation_isStableEquivalence j (0)

example : IsIso
    ((LoopPrespectrum.stableHomotopyFunctor (1 : ℤ)).map
      (boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap j)) :=
  boundedAboveFlatAffineSupportedSectionEvaluation_isStableEquivalence j (1)

example (d : ℤ) : IsIso
    ((LoopPrespectrum.stableHomotopyFunctor (d : ℤ)).map
      (boundedAboveFlatAffineSupportedSectionEvaluationPrespectrumMap j)) :=
  boundedAboveFlatAffineSupportedSectionEvaluation_isStableEquivalence j (d)
