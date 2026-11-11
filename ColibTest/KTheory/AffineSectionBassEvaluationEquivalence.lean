/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassEvaluationEquivalence

/-! Actual-map consumers for complete levelwise and stable affine Bass evaluation. -/

open CategoryTheory AlgebraicGeometry.Scheme.Modules Topology.LoopPrespectrum
open Topology

universe u
variable (R : CommRingCat.{u})

example (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedAboveFlatAffineSectionBassSpanEvaluation R).map n) :=
  boundedAboveFlatAffineSectionBassSpanEvaluation_level_isWeakHomotopyEquivalence R n

example : IsWeakHomotopyEquivalence ((boundedAboveFlatAffineSectionBassSpanEvaluation R).map 0) :=
  boundedAboveFlatAffineSectionBassSpanEvaluation_level_isWeakHomotopyEquivalence R 0

example : IsStableEquivalence (boundedAboveFlatAffineSectionBassSpanEvaluation R) :=
  boundedAboveFlatAffineSectionBassSpanEvaluation_isStableEquivalence R

example (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedAboveFlatAffineSectionBassConeEvaluation R).map n) :=
  boundedAboveFlatAffineSectionBassConeEvaluation_level_isWeakHomotopyEquivalence R n

example : IsWeakHomotopyEquivalence ((boundedAboveFlatAffineSectionBassConeEvaluation R).map 0) :=
  boundedAboveFlatAffineSectionBassConeEvaluation_level_isWeakHomotopyEquivalence R 0

example : IsStableEquivalence (boundedAboveFlatAffineSectionBassConeEvaluation R) :=
  boundedAboveFlatAffineSectionBassConeEvaluation_isStableEquivalence R

example (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedAboveFlatAffineSectionBassStepEvaluation R).map n) :=
  boundedAboveFlatAffineSectionBassStepEvaluation_level_isWeakHomotopyEquivalence R n

example : IsWeakHomotopyEquivalence ((boundedAboveFlatAffineSectionBassStepEvaluation R).map 0) :=
  boundedAboveFlatAffineSectionBassStepEvaluation_level_isWeakHomotopyEquivalence R 0

example : IsStableEquivalence (boundedAboveFlatAffineSectionBassStepEvaluation R) :=
  boundedAboveFlatAffineSectionBassStepEvaluation_isStableEquivalence R

example (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassSpanEvaluation R)) :=
  boundedAboveFlatAffineSectionBassSpanEvaluation_isStableEquivalence R d

example (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassConeEvaluation R)) :=
  boundedAboveFlatAffineSectionBassConeEvaluation_isStableEquivalence R d

example (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassStepEvaluation R)) :=
  boundedAboveFlatAffineSectionBassStepEvaluation_isStableEquivalence R d
