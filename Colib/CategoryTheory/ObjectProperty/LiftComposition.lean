/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.EqToHom

/-!
# Composition of original functors lifted through object properties

The literal lift-composition identities isolate the categorical calculation from the potentially
large membership proofs of geometric full subcategories. They preserve every original object and
map and support naturality descent through the fully faithful inclusion.
-/
@[expose] public section
open CategoryTheory
universe u₁ v₁ u₂ v₂ u₃ v₃
namespace CategoryTheory.ObjectProperty
variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    (P : CategoryTheory.ObjectProperty B) (Q : CategoryTheory.ObjectProperty C)
    (F : A ⥤ B) (G : B ⥤ C) (hF : ∀ X, P (F.obj X))
    (hG : ∀ X : P.FullSubcategory, Q (G.obj X.obj))

/-- Forget the property of an actual lifted functor without expanding its original maps. -/
@[colib_ref "quillen" "Quillen/Aglib/CategoryTheory/ObjectProperty/LiftComposition.lean:29"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem lift_comp_ι : P.lift F hF ⋙ P.ι = F := rfl

/-- Compose two specified forgetful squares without unfolding any of their original functors. -/
@[colib_ref "quillen" "Quillen/Aglib/CategoryTheory/ObjectProperty/LiftComposition.lean:32"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem comp_forget_eq {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (P : CategoryTheory.ObjectProperty A) (Q : CategoryTheory.ObjectProperty B)
    (T : CategoryTheory.ObjectProperty D)
    (F : P.FullSubcategory ⥤ Q.FullSubcategory) (G : Q.FullSubcategory ⥤ T.FullSubcategory)
    (H : A ⥤ B) (K : B ⥤ C) (L : C ⥤ D)
    (hF : F ⋙ Q.ι = P.ι ⋙ H) (hG : G ⋙ T.ι = Q.ι ⋙ K ⋙ L) :
    (F ⋙ G) ⋙ T.ι = P.ι ⋙ (H ⋙ K) ⋙ L := by
  rw [Functor.assoc, hG, ← Functor.assoc F Q.ι, hF]
  simp only [Functor.assoc]

/-- Pasting an original forgetful square with its specified comparison retains every functor. -/
@[colib_ref "quillen" "Quillen/Aglib/CategoryTheory/ObjectProperty/LiftComposition.lean:43"
  "adaptation" "Actual union-support coefficient sections, chosen zero and exact Model maps"]
theorem comp_forget_eq_of_comparison {A B C D E : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
    (P : CategoryTheory.ObjectProperty A) (Q : CategoryTheory.ObjectProperty B)
    (R : CategoryTheory.ObjectProperty C)
    (F : P.FullSubcategory ⥤ Q.FullSubcategory) (G : Q.FullSubcategory ⥤ R.FullSubcategory)
    (I : A ⥤ D) (J : D ⥤ B) (K : B ⥤ C) (L : D ⥤ E) (M : E ⥤ C)
    (hF : F ⋙ Q.ι = P.ι ⋙ I ⋙ J) (hG : G ⋙ R.ι = Q.ι ⋙ K)
    (hL : L ⋙ M = J ⋙ K) :
    (F ⋙ G) ⋙ R.ι = P.ι ⋙ (I ⋙ L) ⋙ M := by
  rw [Functor.assoc, hG, ← Functor.assoc F Q.ι, hF]
  simp only [Functor.assoc]
  rw [← hL]

/-- Lift a specified underlying natural iso along the actual fully faithful inclusion. -/
@[colib_ref "quillen" "Quillen/Aglib/CategoryTheory/ObjectProperty/LiftComposition.lean:57"
  "adaptation" "Actual supported evaluation iso lifted through the fully faithful inclusion"]
noncomputable def isoOfForgetIso {A B : Type*} [Category* A] [Category* B]
    (P : CategoryTheory.ObjectProperty B) (F G : A ⥤ P.FullSubcategory)
    (F₀ G₀ : A ⥤ B) (hF : F ⋙ P.ι = F₀) (hG : G ⋙ P.ι = G₀) (e : F₀ ≅ G₀) : F ≅ G :=
  Functor.fullyFaithfulCancelRight P.ι (eqToIso hF ≪≫ e ≪≫ (eqToIso hG).symm)

end CategoryTheory.ObjectProperty

