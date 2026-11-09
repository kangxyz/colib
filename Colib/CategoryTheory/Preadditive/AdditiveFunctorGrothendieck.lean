/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Preadditive.LiftedAdditiveYoneda

/-!
Implementation adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Aglib/CategoryTheory/AdditiveFunctorGrothendieck.lean`,
blob `6b3ac7843c24bc3d055b708902e35f2d154c0034`.

# Additive abelian presheaves form a Grothendieck category

Exact filtered colimits are computed through the actual additive-functor
inclusion. A separator is the coproduct of lifted additive representables.
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.AdditiveFunctor

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- Additive abelian presheaves, with coefficient universe containing the source
objects and arrows, form a genuine Grothendieck abelian category. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/CategoryTheory/AdditiveFunctorGrothendieck.lean:26-27"
  "adaptation" "Actual additive functors, lifted representables and transfer sheaf reflection"]
instance isGrothendieckAbelian :
    IsGrothendieckAbelian.{max u v} (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v}) where

end CategoryTheory.AdditiveFunctor
