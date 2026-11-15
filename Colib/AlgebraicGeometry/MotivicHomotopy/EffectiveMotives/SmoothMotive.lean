/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Representable

/-! # The original effective motive of a smooth scheme -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

/-- The existing singular motive of a smooth scheme with its actual graph maps. -/
abbrev effectiveSmoothMotive : SmoothSite (Spec (.of k)) ⥤ EffectiveMotivesMinus k :=
  Cor.graphFunctor k ⋙ effectiveMotive k

end AlgebraicGeometry.MotivicHomotopy
