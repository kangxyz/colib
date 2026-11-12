/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryBottomSource

/-! # The original bottom-source map is invertible on every finite S-stage diagram -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
universe u
namespace ColibTest.OriginalParameterAuxiliaryBottomSource

/-- Every original finite S-stage retains invertibility of the actual bottom-source map. -/
theorem toBasic_stage_isIso (Q : Scheme.{u}) (U : Q.Opens) (n : ℕ) :
    IsIso (Functor.whiskerRight (toBasic U.ι ⊥) (stages n)) := by
  infer_instance

end ColibTest.OriginalParameterAuxiliaryBottomSource
