/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.ChangeExact
public import Colib.CategoryTheory.Triangulated.Stabilization.Monoidal.Exactness
public import Colib.CategoryTheory.Triangulated.Stabilization.Monoidal.Transport
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Exactness of the transported stable tensor

Tensoring with a fixed object for the transported monoidal structure is
conjugation of the original finite-stage tensor functor by the change of
transition. Its shift comparison uses the original tensor shift and the
compatible shifts of that equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory

universe u v

namespace CategoryTheory.Stabilization

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  {T : C ⥤ C} [T.Full] [T.Faithful] (L : C)
  [(tensorRight L).Full] [(tensorRight L).Faithful]
  (e : tensorRight L ≅ T) (hL : (β_ L L).hom = 𝟙 _)

/-- The transported left tensor is the conjugate of the original stable left tensor. -/
def transportedTensorLeftIso (B : Stabilization T) :
    letI := monoidalCategory L hL
    letI := transportedMonoidalCategory L e hL
    (changeEquivalence e).inverse ⋙ tensorLeft ((changeEquivalence e).inverse.obj B) ⋙
      (changeEquivalence e).functor ≅ tensorLeft B :=
  Iso.refl _

/-- The transported right tensor is the conjugate of the original stable right tensor. -/
def transportedTensorRightIso (B : Stabilization T) :
    letI := monoidalCategory L hL
    letI := transportedMonoidalCategory L e hL
    (changeEquivalence e).inverse ⋙ tensorRight ((changeEquivalence e).inverse.obj B) ⋙
      (changeEquivalence e).functor ≅ tensorRight B :=
  Iso.refl _

variable [HasShift C ℤ] [(tensorRight L).CommShift ℤ] [T.CommShift ℤ]
  [NatTrans.CommShift e.hom ℤ]

/-- The shift structure on the forward functor induced by changing the transition. -/
local instance changeEquivalenceFunctorCommShift : (changeEquivalence e).functor.CommShift ℤ :=
  inferInstanceAs ((changeFunctor e).CommShift ℤ)

/-- The shift structure on the inverse functor of the change of transition equivalence. -/
local instance changeEquivalenceInverseCommShift : (changeEquivalence e).inverse.CommShift ℤ :=
  (changeEquivalence e).commShiftInverse ℤ

variable (B : Stabilization T)
  [(tensorLeft ((changeEquivalence e).inverse.obj B).obj).CommShift ℤ]
  [NatTrans.CommShift (tensorLeftTwistIso L ((changeEquivalence e).inverse.obj B).obj).hom ℤ]

/-- The transported left tensor uses the shift of the actual finite-stage tensor. -/
@[instance_reducible]
def transportedTensorLeftCommShift :
    letI := transportedMonoidalCategory L e hL
    (tensorLeft B).CommShift ℤ := by
  letI := monoidalCategory L hL
  letI := transportedMonoidalCategory L e hL
  letI := stableTensorLeftCommShift L ((changeEquivalence e).inverse.obj B) hL
  exact Functor.CommShift.ofIso (transportedTensorLeftIso L e hL B) ℤ

/-- The transported right tensor uses the shift of the actual finite-stage tensor. -/
@[instance_reducible]
def transportedTensorRightCommShift :
    letI := transportedMonoidalCategory L e hL
    (tensorRight B).CommShift ℤ := by
  letI := monoidalCategory L hL
  letI := symmetricCategory L hL
  letI := transportedMonoidalCategory L e hL
  letI := stableTensorRightCommShift L ((changeEquivalence e).inverse.obj B) hL
  exact Functor.CommShift.ofIso (transportedTensorRightIso L e hL B) ℤ

variable [Preadditive C] [MonoidalPreadditive C] [T.Additive] [HasZeroObject C]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [(tensorRight L).IsTriangulated] [T.IsTriangulated]
  [(tensorLeft ((changeEquivalence e).inverse.obj B).obj).IsTriangulated]

omit [SymmetricCategory C] in
private theorem changeEquivalenceInverseIsTriangulated :
    (changeEquivalence e).inverse.IsTriangulated := by
  let : (changeEquivalence e).CommShift ℤ := (changeEquivalence e).commShift_of_functor ℤ
  have h : (changeEquivalence e).functor.IsTriangulated :=
    inferInstanceAs ((changeFunctor e).IsTriangulated)
  exact (Equivalence.IsTriangulated.mk' (changeEquivalence e) h).rightAdjoint_isTriangulated

/-- The left tensor of the transported stable structure preserves distinguished triangles. -/
theorem transportedTensorLeft_isTriangulated :
    letI := transportedMonoidalCategory L e hL
    letI := transportedTensorLeftCommShift L e hL B
    (tensorLeft B).IsTriangulated := by
  let := monoidalCategory L hL
  let := transportedMonoidalCategory L e hL
  let := stableTensorLeftCommShift L ((changeEquivalence e).inverse.obj B) hL
  let := transportedTensorLeftCommShift L e hL B
  let : (changeEquivalence e).functor.IsTriangulated :=
    inferInstanceAs ((changeFunctor e).IsTriangulated)
  let : (changeEquivalence e).inverse.IsTriangulated := changeEquivalenceInverseIsTriangulated L e
  let := stableTensorLeft_isTriangulated L ((changeEquivalence e).inverse.obj B) hL
  let := Functor.CommShift.ofIso_compatibility (transportedTensorLeftIso L e hL B) ℤ
  exact Functor.isTriangulated_of_iso (transportedTensorLeftIso L e hL B)

/-- The right tensor of the transported stable structure preserves distinguished triangles. -/
theorem transportedTensorRight_isTriangulated :
    letI := transportedMonoidalCategory L e hL
    letI := transportedTensorRightCommShift L e hL B
    (tensorRight B).IsTriangulated := by
  let := monoidalCategory L hL
  let := symmetricCategory L hL
  let := transportedMonoidalCategory L e hL
  let := stableTensorRightCommShift L ((changeEquivalence e).inverse.obj B) hL
  let := transportedTensorRightCommShift L e hL B
  let : (changeEquivalence e).functor.IsTriangulated :=
    inferInstanceAs ((changeFunctor e).IsTriangulated)
  let : (changeEquivalence e).inverse.IsTriangulated := changeEquivalenceInverseIsTriangulated L e
  let := stableTensorRight_isTriangulated L ((changeEquivalence e).inverse.obj B) hL
  let := Functor.CommShift.ofIso_compatibility (transportedTensorRightIso L e hL B) ℤ
  exact Functor.isTriangulated_of_iso (transportedTensorRightIso L e hL B)

end CategoryTheory.Stabilization
