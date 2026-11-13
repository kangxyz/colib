/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.RingTheory.KTheory.Quillen.Field.FiniteFieldKTwo
public import Colib.RingTheory.KTheory.GTheory.FiniteModules.FractionLocalization
public import Colib.KTheory.Quillen.Map.SmallModelUniverse

/-!
# Native finite-module G₂ of a finite field

The canonical change of small-model universe for the same exact category
transports the upper finite-module K₂ vanishing to the original native G₂.
The equivalence retains the actual Q-functor and its canonical zero-object path.

Implementation provenance: `finiteModuleGTwo_subsingleton` and
`finiteModuleGTwo_eq_one` in `Quillen/KTheory/Field/FiniteFieldKTwo.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. This is the ring-theoretic
consumer only; no coherent scheme comparison is asserted.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Field

variable (F : Type u) [Field F] [Finite F]

/-- The original lower finite-module G₂ group is trivial through its canonical upper-model map. -/
theorem finiteModuleGTwo_subsingleton :
    Subsingleton (FGModuleCat.FractionLocalization.G.{u, u} F 2) := by
  constructor
  intro a b
  apply ((abelianExactStructure (FGModuleCat.{u} F)).smallKUniverseEquiv.{u, u + 1} 2).injective
  exact @Subsingleton.elim _ (upperModuleKTwo_subsingleton F) _ _

/-- Every class in the original native finite-module G₂ group of a finite field is neutral. -/
theorem finiteModuleGTwo_eq_one (a : FGModuleCat.FractionLocalization.G.{u, u} F 2) : a = 1 :=
  @Subsingleton.elim _ (finiteModuleGTwo_subsingleton F) a 1

attribute [colib_tag "COL-0280",
  colib_ref "quillen"
    "Quillen/KTheory/Field/FiniteFieldKTwo.lean, finiteModuleGTwo clauses" "adaptation"
    "The original lower finite-module G2 via the same-category small-model universe comparison"]
  finiteModuleGTwo_subsingleton finiteModuleGTwo_eq_one

end Quillen.Field
