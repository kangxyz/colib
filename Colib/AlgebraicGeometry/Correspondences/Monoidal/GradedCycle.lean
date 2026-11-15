/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatFundamental
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs

/-!
# Comparing whole support cycles with their native dimension grade

If the generic components of a Noetherian support all have the displayed
dimension, its ungraded whole fundamental cycle is the underlying cycle of
Stacks' graded fundamental cycle. The condition is on this particular
support, not on every component of a surrounding smooth source.

This is the comparison needed to apply finite flat push-pull to each actual
prime-support product in its own dimension grade. Local lengths are unchanged.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- The identity closed immersion gives the original self-length at each generic point. -/
theorem componentMultiplicity_id_eq_selfLength {X : Scheme.{u}} (x : genericPoints X) :
    componentMultiplicity (𝟙 X) x =
      ((Module.length (X.presheaf.stalk x.val) (X.presheaf.stalk x.val)).toNat : ℤ) := by
  let A := X.presheaf.stalk x.val
  let fId : A →+* A := ((𝟙 X : X ⟶ X).stalkMap x.val).hom
  have hId : fId = RingHom.id A := by
    dsimp only [fId, A]
    simp only [Scheme.Hom.stalkMap_id]
    rfl
  change ((@Module.length A A _ _ (Module.compHom A fId)).toNat : ℤ) = _
  rw [hId]

/-- Whole and graded fundamental cycles agree when all actual components have that grade. -/
theorem fundamentalCycle_eq_graded_of_genericDimensions (C : ChowSituation.{u})
    {X : Scheme.{u}} [IsNoetherian X] (s : X ⟶ C.S) [LocallyOfFiniteType s]
    (d : ℤ) (hd : ∀ x : genericPoints X, relativeDimension C.dimensionFunction s x.val = d) :
    AlgebraicCycle.fundamentalCycle X = (cycleAssociatedToClosedSubscheme C s (𝟙 X) d).val := by
  classical
  apply Function.locallyFinsuppWithin.ext
  intro x
  by_cases hx : x ∈ genericPoints X
  · calc
      AlgebraicCycle.fundamentalCycle X x =
          ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat : ℤ) :=
        AlgebraicCycle.fundamentalCycle_apply_generic X ⟨x, hx⟩
      _ = componentMultiplicity (𝟙 X) ⟨x, hx⟩ :=
        (componentMultiplicity_id_eq_selfLength ⟨x, hx⟩).symm
      _ = (cycleAssociatedToClosedSubscheme C s (𝟙 X) d).val x :=
        (cycleAssociatedToClosedSubscheme_apply C s (𝟙 X) d ⟨x, hx⟩ (hd ⟨x, hx⟩)).symm
  · rw [AlgebraicCycle.fundamentalCycle_apply_of_notMem X x hx]
    symm
    apply cycleAssociatedToClosedSubscheme_apply_eq_zero C s (𝟙 X) d x
    rintro ⟨a, ha, _⟩
    exact hx (ha ▸ a.property)

end Stacks.Chow
