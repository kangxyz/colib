/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.RingTheory.KTheory.Quillen.Field.FiniteFieldGTwo
public import Mathlib.Algebra.Field.ZMod

/-! The original lower finite-module G₂ endpoints over the smallest finite fields. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace ColibTest.FiniteFieldGTwo

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Every original native lower-module endpoint is trivial over F2, F3 and F5. -/
theorem smallFieldsLowerGTwo :
    Subsingleton (FGModuleCat.FractionLocalization.G.{0, 0} (ZMod 2) 2) ∧
      Subsingleton (FGModuleCat.FractionLocalization.G.{0, 0} (ZMod 3) 2) ∧
        Subsingleton (FGModuleCat.FractionLocalization.G.{0, 0} (ZMod 5) 2) :=
  ⟨Quillen.Field.finiteModuleGTwo_subsingleton (ZMod 2),
    Quillen.Field.finiteModuleGTwo_subsingleton (ZMod 3),
    Quillen.Field.finiteModuleGTwo_subsingleton (ZMod 5)⟩

end ColibTest.FiniteFieldGTwo
