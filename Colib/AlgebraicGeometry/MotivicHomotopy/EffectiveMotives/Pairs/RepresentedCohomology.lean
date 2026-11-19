/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Basic
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Triangulated
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-! # Cohomology represented by the relative effective motive -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Cohomology with an effective coefficient is contravariant in the original open pair. -/
def effectivePairCohomology (K : EffectiveMotivesMinus k) (n : ℤ) :
    (Arrow (SmoothSite (Spec (CommRingCat.of k))))ᵒᵖ ⥤ AddCommGrpCat.{w'} :=
  (effectivePairMotiveFunctor k).op ⋙ preadditiveYoneda.obj (K⟦n⟧)

end AlgebraicGeometry.MotivicHomotopy
