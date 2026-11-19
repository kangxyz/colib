/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.Embedding.DownNatTensorDegree
public import Colib.Algebra.Homology.Embedding.DownNatTensorCancellation

/-! # Inverse identities for the actual down-natural total degree maps

These are identities of degree maps, not yet an isomorphism of complexes.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits ComplexShape
namespace HomologicalComplex.DownNatTensor

variable {A B D : Type*} [Category* A] [Category* B] [Category* D]
  [HasZeroMorphisms A] [HasZeroObject A] [HasZeroMorphisms B] [HasZeroObject B]
  [Preadditive D] [HasZeroObject D]
  (F : A ⥤ B ⥤ D) [F.PreservesZeroMorphisms]
  [∀ X, (F.obj X).PreservesZeroMorphisms]
  (K : ChainComplex A ℕ) (L : ChainComplex B ℕ)
  [HasMapBifunctor K L F (down ℕ)]
  [HasMapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)]

/-- The reverse-then-forward composite fixes the actual extended natural total. -/
theorem reverseDegree_forwardDegree (n : ℕ) :
    reverseDegree F K L n ≫ forwardDegree F K L n = 𝟙 _ := by
  let e := (mapBifunctor K L F (down ℕ)).extendXIso embeddingDownNat (i := n) rfl
  apply (cancel_epi e.inv).mp
  apply mapBifunctor.hom_ext
  intro p q hpq
  have h : p + q = n := by simpa using hpq
  let a := ιMapBifunctor K L F (down ℕ) p q n hpq
  let b := ιMapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat)
    F (up ℤ) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) (retained_total_index p q n h)
  have hr : a ≫ e.inv ≫ reverseDegree F K L n = reverseSummand F K L p q ≫ b := by
    simpa only [a, b, e, reverseSummand, Category.assoc] using
      inclusion_reverseDegree F K L p q n h
  change a ≫ (e.inv ≫ (reverseDegree F K L n ≫ forwardDegree F K L n)) =
    a ≫ (e.inv ≫ 𝟙 _)
  calc
    _ = (a ≫ e.inv ≫ reverseDegree F K L n) ≫ forwardDegree F K L n := by
      simp only [Category.assoc]
    _ = (reverseSummand F K L p q ≫ b) ≫ forwardDegree F K L n := by rw [hr]
    _ = reverseSummand F K L p q ≫ retainedComponent F K L p q n h := by
      rw [Category.assoc]
      dsimp only [b]
      rw [inclusion_forwardDegree, component_neg_nat]
    _ = a ≫ e.inv := by
      rw [reverseSummand_eq_inv]
      simp [retainedComponent, retainedSummandIso, a, e, Category.assoc]
    _ = _ := by simp only [Category.comp_id]


/-- The retained forward component followed by the reverse total map is the
original integer-total inclusion. -/
theorem retainedComponent_reverseDegree (p q n : ℕ) (h : p + q = n) :
    retainedComponent F K L p q n h ≫ reverseDegree F K L n =
      ιMapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat)
        F (up ℤ) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) (retained_total_index p q n h) := by
  simp only [retainedComponent, Category.assoc]
  rw [inclusion_reverseDegree F K L p q n h]
  simp

/-- The forward-then-reverse composite fixes the integer total, including its
zero summands outside the retained negative quadrant. -/
theorem forwardDegree_reverseDegree (n : ℕ) :
    forwardDegree F K L n ≫ reverseDegree F K L n = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro i j hij
  by_cases hi : i ≤ 0
  · by_cases hj : j ≤ 0
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨q, rfl⟩ : ∃ q : ℕ, j = -(q : ℤ) := ⟨(-j).toNat, by omega⟩
      have h : p + q = n := by dsimp at hij; omega
      rw [← Category.assoc, inclusion_forwardDegree, component_neg_nat F K L p q n h,
        retainedComponent_reverseDegree]
      simp only [Category.comp_id]
    · exact (isZero_summand F K L i j (Or.inr (by omega))).eq_of_src _ _
  · exact (isZero_summand F K L i j (Or.inl (by omega))).eq_of_src _ _

end HomologicalComplex.DownNatTensor
