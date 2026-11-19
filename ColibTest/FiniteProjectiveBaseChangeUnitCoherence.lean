/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUniversal

/-!
# Independently universed original scalar-extension units

Downstream use retains the original comparison maps and their actual units.
The composition formula also respects arbitrary right scalar multiplication,
without placing the three rings in a common universe.
-/

@[expose] public section

noncomputable section

universe u v w

open MulOpposite ModuleCat.FiniteProjective

namespace ColibTest.FiniteProjectiveBaseChangeUnitCoherence

variable {R : Type u} {S : Type v} {T : Type w} [Ring R] [Ring S] [Ring T]

example (P : Category.{u, u} Rᵐᵒᵖ) (x : P.obj) :
    (rightBaseChangeId.hom.app P).hom.hom (rightBaseChangeUnit (RingHom.id R) P x) = x :=
  rightBaseChangeId_hom_unit P x

example (f : R →+* S) (g : S →+* T) (P : Category.{u, u} Rᵐᵒᵖ)
    (x : P.obj) (r : R) :
    ((rightBaseChangeComp f g).hom.app P).hom.hom
        (rightBaseChangeUnit g ((rightBaseChange f).obj P)
          (rightBaseChangeUnit f P (op r • x))) =
      op (g (f r)) • rightBaseChangeUnit (g.comp f) P x := by
  rw [rightBaseChangeComp_hom_unit]
  exact (rightBaseChangeUnit (g.comp f) P).map_smulₛₗ (op r) x

end ColibTest.FiniteProjectiveBaseChangeUnitCoherence
