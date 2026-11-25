/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationEquivalence

open AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation

universe u

#check comparisonHomotopy_inl
#check comparisonHomotopy_inr
#check comparisonHomotopy_cylinder
#check coneEvaluation_inclusion
#check sectionStep_eq

example (X : Scheme.{u}) (n : ℕ) :
    IsWeakHomotopyEquivalence ((spanEvaluation X).map n) :=
  spanEvaluation_level_isWeakHomotopyEquivalence X n

example (X : Scheme.{u}) (n : ℕ) :
    IsWeakHomotopyEquivalence ((coneEvaluation X).map n) :=
  coneEvaluation_level_isWeakHomotopyEquivalence X n

example (X : Scheme.{u}) :
    IsWeakHomotopyEquivalence ((stepEvaluation X).map 0) :=
  stepEvaluation_level_isWeakHomotopyEquivalence X 0

example (X : Scheme.{u}) : IsStableEquivalence (stepEvaluation X) :=
  stepEvaluation_isStableEquivalence X
