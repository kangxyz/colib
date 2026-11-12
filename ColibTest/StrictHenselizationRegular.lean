/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Etale.StrictHenselizationRegular
import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

open CategoryTheory AlgebraicGeometry

universe u

/-- An actual smooth object over any field supplies the regularity of the original base;
the strict-local scheme itself is not assumed to be smooth over that field. -/
example (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [Smooth f]
    (B : BigEtaleSite.{u}) (hX : B.Contains X) (s : GeometricPoint X) :
    IsRegular (strictHenselization B X hX s) ∧
      IsNoetherian (strictHenselization B X hX s) ∧
      IsIntegral (strictHenselization B X hX s) := by
  have hreg := isRegular_of_smooth_over_field f
  exact ⟨isRegular_strictHenselization_of_isRegular B X hX s hreg,
    isNoetherian_strictHenselization_of_isRegular B X hX s hreg,
    isIntegral_strictHenselization_of_isRegular B X hX s hreg⟩

/-- Noetherianity needs neither smoothness nor regularity of the original scheme. -/
example (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S) [IsLocallyNoetherian S] :
    IsNoetherian (strictHenselization B S hS s) :=
  isNoetherian_strictHenselization B S hS s
