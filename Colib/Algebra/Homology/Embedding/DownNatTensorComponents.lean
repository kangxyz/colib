/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Actual summands for the chain-to-cochain tensor comparison

The upstream `MapBifunctorExtend` treats `up ℕ` and `embeddingUpNat`; it cannot
be applied to the original chains. Here the retained summands and their signs
are constructed for `down ℕ` and `embeddingDownNat`. This file does not yet
assemble a chain map or assert invertibility of a comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits ComplexShape
namespace HomologicalComplex.DownNatTensor

variable {A B D : Type*} [Category* A] [Category* B] [Category* D]
  [HasZeroMorphisms A] [HasZeroObject A] [HasZeroMorphisms B] [HasZeroObject B]
  [Preadditive D] [HasZeroObject D]
  (F : A ⥤ B ⥤ D) [F.PreservesZeroMorphisms]
  [∀ X, (F.obj X).PreservesZeroMorphisms]
  (K : ChainComplex A ℕ) (L : ChainComplex B ℕ)

/-- A positive index is outside the original nonpositive extension. -/
theorem isZero_summand (i j : ℤ) (h : 0 < i ∨ 0 < j) :
    IsZero ((F.obj ((K.extend embeddingDownNat).X i)).obj
      ((L.extend embeddingDownNat).X j)) := by
  rcases h with h | h
  · exact (F.map_isZero (CochainComplex.isZero_of_isStrictlyLE _ 0 i h)).obj _
  · exact (F.obj _).map_isZero (CochainComplex.isZero_of_isStrictlyLE _ 0 j h)

/-- Negating the actual homological index leaves its Koszul sign unchanged. -/
theorem sign_neg_nat (p : ℕ) : (up ℤ).ε (-(p : ℤ)) = (down ℕ).ε p := by
  rw [ε_up_ℤ, Int.negOnePow_neg, ε_down_ℕ]
  ext
  rw [Int.coe_negOnePow_natCast]
  push_cast
  rfl

variable [HasMapBifunctor K L F (down ℕ)]

/-- On an original bidegree `(p,q)` the comparison is the actual total-summand
inclusion, conjugated by the native extension isomorphisms. -/
def retainedComponent (p q n : ℕ) (h : p + q = n) :
    (F.obj ((K.extend embeddingDownNat).X (-(p : ℤ)))).obj
      ((L.extend embeddingDownNat).X (-(q : ℤ))) ⟶
    ((mapBifunctor K L F (down ℕ)).extend embeddingDownNat).X (-(n : ℤ)) :=
  (F.map (K.extendXIso embeddingDownNat (i := p) rfl).hom).app _ ≫
    (F.obj (K.X p)).map (L.extendXIso embeddingDownNat (i := q) rfl).hom ≫
    ιMapBifunctor K L F (down ℕ) p q n (by simpa using h) ≫
    ((mapBifunctor K L F (down ℕ)).extendXIso embeddingDownNat (i := n) rfl).inv

/-- The integer total index of each retained summand is precisely the extended
original total index. -/
theorem retained_total_index (p q n : ℕ) (h : p + q = n) :
    -(p : ℤ) + -(q : ℤ) = -(n : ℤ) := by omega

end HomologicalComplex.DownNatTensor
