/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.CategoryTheory.Endofunctor.FixedWords
noncomputable section
open CategoryTheory
universe u v
namespace CategoryTheory.Functor.FixedWords
variable {D : Type u} [Category.{v} D]

example (F : D ⥤ D) (n : ℕ) : F ⋙ power F n = power F (n + 1) :=
  power_succ_left F n

example (F : D ⥤ D) (P : F ⋙ F ≅ F ⋙ F) (i : ℕ) (X : D) :
    (beta F P (i + 1)).hom.app X =
      P.hom.app ((power F i).obj X) ≫ F.map ((beta F P i).hom.app X) :=
  beta_succ_hom_app F P i X

example (F : D ⥤ D) (P : F ⋙ F ≅ F ⋙ F) (i : ℕ) (X : D) :
    (fixedWord F P (i + 1)).hom.app X =
      F.map ((fixedWord F P i).hom.app X) ≫ (beta F P i).hom.app X :=
  fixedWord_succ_hom_app F P i X

example (F : D ⥤ D) (P : F ⋙ F ≅ F ⋙ F) : fixedWord F P 2 = P :=
  fixedWord_two F P

example (F : D ⥤ D) (P : F ⋙ F ≅ F ⋙ F) :
    fixedWord F P 3 =
      Functor.isoWhiskerRight P F ≪≫ Functor.associator F F F ≪≫
      Functor.isoWhiskerLeft F P ≪≫ (Functor.associator F F F).symm ≪≫
      Functor.isoWhiskerRight P F :=
  fixedWord_three F P

example (F : D ⥤ D) (P : F ⋙ F ≅ F ⋙ F) (X : D) :
    (fixedWord F P 3).hom.app X =
      F.map (P.hom.app X) ≫ P.hom.app (F.obj X) ≫ F.map (P.hom.app X) :=
  fixedWord_three_hom_app F P X

end CategoryTheory.Functor.FixedWords
end
