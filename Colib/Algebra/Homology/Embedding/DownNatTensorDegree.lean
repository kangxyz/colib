/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.Embedding.DownNatTensorComponents

/-!
# Degree maps for the original down-natural tensor comparison

Both maps are assembled from the actual coproduct inclusions. This file keeps
the degree maps separate from the still-required chain-map and inverse proofs.
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

/-- An arbitrary integer-indexed summand maps to its corresponding original
summand if both indices are retained, and to zero otherwise. -/
def component (n : ℕ) (i j : ℤ) (hij : i + j = -(n : ℤ)) :
    (F.obj ((K.extend embeddingDownNat).X i)).obj ((L.extend embeddingDownNat).X j) ⟶
      ((mapBifunctor K L F (down ℕ)).extend embeddingDownNat).X (-(n : ℤ)) :=
  if h : i ≤ 0 ∧ j ≤ 0 then
    (F.map (K.extendXIso embeddingDownNat (i := (-i).toNat)
      (by change -((-i).toNat : ℤ) = i; omega)).hom).app _ ≫
      (F.obj (K.X (-i).toNat)).map
        (L.extendXIso embeddingDownNat (i := (-j).toNat)
          (by change -((-j).toNat : ℤ) = j; omega)).hom ≫
      ιMapBifunctor K L F (down ℕ) (-i).toNat (-j).toNat n (by dsimp; omega) ≫
      ((mapBifunctor K L F (down ℕ)).extendXIso embeddingDownNat (i := n) rfl).inv
  else 0

/-- The forward map in each retained total degree. -/
def forwardDegree (n : ℕ) :
    (mapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)).X
      (-(n : ℤ)) ⟶
    ((mapBifunctor K L F (down ℕ)).extend embeddingDownNat).X (-(n : ℤ)) :=
  mapBifunctorDesc (fun i j hij => component F K L n i j hij)

/-- The forward degree map acts on every summand by the displayed concrete formula. -/
@[reassoc (attr := simp)]
theorem inclusion_forwardDegree (n : ℕ) (i j : ℤ) (hij : i + j = -(n : ℤ)) :
    ιMapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)
      i j (-(n : ℤ)) hij ≫ forwardDegree F K L n = component F K L n i j hij :=
  ι_mapBifunctorDesc _ i j hij

/-- The reverse map uses the original finite antidiagonal and the inverse
extension identifications, with no choice of replacement complex. -/
def reverseDegree (n : ℕ) :
    ((mapBifunctor K L F (down ℕ)).extend embeddingDownNat).X (-(n : ℤ)) ⟶
    (mapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)).X
      (-(n : ℤ)) :=
  ((mapBifunctor K L F (down ℕ)).extendXIso embeddingDownNat (i := n) rfl).hom ≫
    mapBifunctorDesc (fun p q hpq =>
      (F.map (K.extendXIso embeddingDownNat (i := p) rfl).inv).app _ ≫
      (F.obj ((K.extend embeddingDownNat).X (-(p : ℤ)))).map
        (L.extendXIso embeddingDownNat (i := q) rfl).inv ≫
      ιMapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)
        (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) (by dsimp at hpq ⊢; omega))

omit [HasMapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)] in
/-- On each retained bidegree, the branch in the forward map is exactly the
original summand formula, with no additional scalar or reindexing map. -/
theorem component_neg_nat (p q n : ℕ) (h : p + q = n) :
    component F K L n (-(p : ℤ)) (-(q : ℤ))
      (retained_total_index p q n h) = retainedComponent F K L p q n h := by
  cases p <;> cases q
  all_goals
    unfold component
    split
    · rfl
    · rename_i hn
      exact False.elim (hn ⟨by omega, by omega⟩)

/-- The reverse map recovers its concrete summand formula after the native
extension tail cancels. This is the first cancellation required for the inverse law. -/
@[reassoc]
theorem inclusion_reverseDegree (p q n : ℕ) (h : p + q = n) :
    ιMapBifunctor K L F (down ℕ) p q n (by simpa using h) ≫
      ((mapBifunctor K L F (down ℕ)).extendXIso embeddingDownNat (i := n) rfl).inv ≫
        reverseDegree F K L n =
    (F.map (K.extendXIso embeddingDownNat (i := p) rfl).inv).app _ ≫
      (F.obj ((K.extend embeddingDownNat).X (-(p : ℤ)))).map
        (L.extendXIso embeddingDownNat (i := q) rfl).inv ≫
      ιMapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)
        (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) (retained_total_index p q n h) := by
  dsimp only [reverseDegree]
  rw [Iso.inv_hom_id_assoc, ι_mapBifunctorDesc]

omit [HasMapBifunctor K L F (down ℕ)] in
/-- The integer antidiagonal has only zero summands in a positive total degree. -/
theorem isZero_total_positive (n : ℤ) (hn : 0 < n) :
    IsZero ((mapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat)
      F (up ℤ)).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply mapBifunctor.hom_ext
  intro i j hij
  exact (isZero_summand F K L i j (by dsimp at hij; omega)).eq_of_src _ _

end HomologicalComplex.DownNatTensor
