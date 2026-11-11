/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Colib.Util.References

/-!
# Fixed finite words from a local square isomorphism

An endofunctor and an actual natural automorphism of its square determine two specified
finite words by ordinary whiskering and the original associator. The power association and
both recursive component formulas are explicit. No braid, involution, permutation action,
or independence of the chosen word is assumed or asserted.

These words are specified by the local square isomorphism and its actual associators.
No Bass objects or geometric assumptions enter the construction.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v
namespace CategoryTheory.Functor.FixedWords
variable {D : Type u} [Category.{v} D]

/-- Right-associated application of an endofunctor, with explicit functor composition. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Endofunctor/FixedWords.lean:30"
  "adaptation" "Original specified finite words with complete functor association."]
def power (F : D ⥤ D) : ℕ → D ⥤ D
  | 0 => 𝟭 D
  | n + 1 => power F n ⋙ F

/-- The defining successor association is equality of complete functors. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Endofunctor/FixedWords.lean:35"
  "adaptation" "Original specified finite words with complete functor association."]
theorem power_succ (F : D ⥤ D) (n : ℕ) : power F (n + 1) = power F n ⋙ F := rfl

/-- Applying one copy first gives the same complete functor, with its equality retained. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Endofunctor/FixedWords.lean:38"
  "adaptation" "Original specified finite words with complete functor association."]
theorem power_succ_left (F : D ⥤ D) (n : ℕ) : F ⋙ power F n = power F (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (F ⋙ power F n) ⋙ F = power F (n + 1) ⋙ F
    exact congrArg (fun G => G ⋙ F) ih

/-- The fixed word that moves the newly inserted factor through the previous block. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Endofunctor/FixedWords.lean:46"
  "adaptation" "Original specified finite words with complete functor association."]
def beta (F : D ⥤ D) (P : F ⋙ F ≅ F ⋙ F) :
    ∀ i : ℕ, power F (i + 1) ≅ power F (i + 1)
  | 0 => Iso.refl _
  | i + 1 => Functor.associator (power F i) F F ≪≫
      Functor.isoWhiskerLeft (power F i) P ≪≫
      (Functor.associator (power F i) F F).symm ≪≫
      Functor.isoWhiskerRight (beta F P i) F

/-- The prescribed accumulated word, without any assertion of word independence. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Endofunctor/FixedWords.lean:55"
  "adaptation" "Original specified finite words with complete functor association."]
def fixedWord (F : D ⥤ D) (P : F ⋙ F ≅ F ⋙ F) :
    ∀ i : ℕ, power F i ≅ power F i
  | 0 => Iso.refl _
  | i + 1 => Functor.isoWhiskerRight (fixedWord F P i) F ≪≫ beta F P i

/-- The initial local word is the identity on the first power. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Endofunctor/FixedWords.lean:61"
  "adaptation" "Original specified finite words with complete functor association."]
theorem beta_zero (F : D ⥤ D) (P : F ⋙ F ≅ F ⋙ F) : beta F P 0 = Iso.refl F := rfl

/-- The actual successor component has the prescribed postcomposition order. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Endofunctor/FixedWords.lean:64"
  "adaptation" "Original specified finite words with complete functor association."]
theorem beta_succ_hom_app (F : D ⥤ D) (P : F ⋙ F ≅ F ⋙ F) (i : ℕ) (X : D) :
    (beta F P (i + 1)).hom.app X =
      P.hom.app ((power F i).obj X) ≫ F.map ((beta F P i).hom.app X) := by
  change 𝟙 _ ≫ P.hom.app ((power F i).obj X) ≫ 𝟙 _ ≫
    F.map ((beta F P i).hom.app X) = _
  simp only [Category.id_comp]

/-- The initial accumulated word retains the identity functor. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Endofunctor/FixedWords.lean:72"
  "adaptation" "Original specified finite words with complete functor association."]
theorem fixedWord_zero (F : D ⥤ D) (P : F ⋙ F ≅ F ⋙ F) :
    fixedWord F P 0 = Iso.refl (𝟭 D) := rfl

/-- The accumulated component first applies the functor to the previous word. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Endofunctor/FixedWords.lean:76"
  "adaptation" "Original specified finite words with complete functor association."]
theorem fixedWord_succ_hom_app (F : D ⥤ D) (P : F ⋙ F ≅ F ⋙ F) (i : ℕ) (X : D) :
    (fixedWord F P (i + 1)).hom.app X =
      F.map ((fixedWord F P i).hom.app X) ≫ (beta F P i).hom.app X := rfl

/-- One local crossing is exactly the supplied square isomorphism. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Endofunctor/FixedWords.lean:81"
  "adaptation" "Original specified finite words with complete functor association."]
theorem beta_one (F : D ⥤ D) (P : F ⋙ F ≅ F ⋙ F) : beta F P 1 = P := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp [beta, power]

/-- The first accumulated word is identity, without imposing a relation on the local map. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Endofunctor/FixedWords.lean:88"
  "adaptation" "Original specified finite words with complete functor association."]
theorem fixedWord_one (F : D ⥤ D) (P : F ⋙ F ≅ F ⋙ F) :
    fixedWord F P 1 = Iso.refl F := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp [fixedWord, beta, power]

/-- The second accumulated word is the given local square isomorphism itself. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Endofunctor/FixedWords.lean:96"
  "adaptation" "Original specified finite words with complete functor association."]
theorem fixedWord_two (F : D ⥤ D) (P : F ⋙ F ≅ F ⋙ F) : fixedWord F P 2 = P := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp [fixedWord, beta, power]

/-- The third word retains the complete functor associator around its middle crossing. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Endofunctor/FixedWords.lean:103"
  "adaptation" "Original specified finite words with complete functor association."]
theorem fixedWord_three (F : D ⥤ D) (P : F ⋙ F ≅ F ⋙ F) :
    fixedWord F P 3 =
      Functor.isoWhiskerRight P F ≪≫ Functor.associator F F F ≪≫
      Functor.isoWhiskerLeft F P ≪≫ (Functor.associator F F F).symm ≪≫
      Functor.isoWhiskerRight P F := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp [fixedWord, beta, power]

/-- Its component is literally the fixed three-factor word, in execution order. -/
@[colib_ref "quillen"
  "Quillen/Aglib/CategoryTheory/Endofunctor/FixedWords.lean:114"
  "adaptation" "Original specified finite words with complete functor association."]
theorem fixedWord_three_hom_app (F : D ⥤ D) (P : F ⋙ F ≅ F ⋙ F) (X : D) :
    (fixedWord F P 3).hom.app X =
      F.map (P.hom.app X) ≫ P.hom.app (F.obj X) ≫ F.map (P.hom.app X) := by
  simp [fixedWord, beta, power]

end CategoryTheory.Functor.FixedWords
