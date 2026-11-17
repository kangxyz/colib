/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Shift.CommShiftTwoFullyFaithful
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive

/-! # Signed shift comparisons for restricted and transported monoidal structures -/

@[expose] public noncomputable section

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Functor.CommShift₂

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
  [Preadditive C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [(curriedTensor C).CommShift₂Int]

/-- The signed shift comparisons of the tensor restricted to a full subcategory,
viewed in the ambient category. -/
@[instance_reducible]
def restrictMonoidalPostcompInt (P : ObjectProperty C) [P.IsMonoidal] [P.IsStableUnderShift ℤ] :
    (curriedTensor P.FullSubcategory ⋙
      (whiskeringRight P.FullSubcategory P.FullSubcategory C).obj P.ι).CommShift₂Int := by
  let I := P.ι
  let T := curriedTensor C
  change ((I ⋙ T) ⋙ (whiskeringLeft P.FullSubcategory C C).obj I).CommShift₂Int
  exact precomp₂ I (I ⋙ T) CommShift₂Setup.int

/-- The signed shift comparisons for the inherited tensor on a full subcategory. -/
@[instance_reducible]
def restrictMonoidalInt (P : ObjectProperty C) [P.IsMonoidal] [P.IsStableUnderShift ℤ] :
    (curriedTensor P.FullSubcategory).CommShift₂Int := by
  let := restrictMonoidalPostcompInt P
  exact ofFullyFaithfulInt P.ι (curriedTensor P.FullSubcategory)

/-- The signed shift comparisons for the tensor transported along an equivalence.
Precompose with the inverse in both variables and postcompose with the forward functor. -/
@[instance_reducible]
def monoidalTransportInt [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] (e : C ≌ D)
    [e.inverse.CommShift ℤ] [e.functor.CommShift ℤ] [e.functor.Additive] :
    letI := CategoryTheory.Monoidal.transport e
    (curriedTensor D).CommShift₂Int := by
  let I : D ⥤ C := e.inverse
  let T : C ⥤ C ⥤ C := curriedTensor C
  let V : C ⥤ D := e.functor
  let T₁ : D ⥤ C ⥤ C := I ⋙ T
  let G : D ⥤ D ⥤ C := T₁ ⋙ (whiskeringLeft D C C).obj I
  let : T₁.CommShift₂Int := precomp₁ I T CommShift₂Setup.int
  let : G.CommShift₂Int := precomp₂ I T₁ CommShift₂Setup.int
  change (G ⋙ (whiskeringRight D C D).obj V).CommShift₂Int
  exact postcompInt G V

end CategoryTheory.Functor.CommShift₂
