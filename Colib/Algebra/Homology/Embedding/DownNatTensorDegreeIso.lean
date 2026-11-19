/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.Embedding.DownNatTensorInverse

/-! # Actual degree isomorphisms and the zero-to-positive differential square

The negative differential square remains a separate obligation. This file
does not assert an isomorphism of complexes.
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
  [HasMapBifunctor K L F (down ℕ)]
  [HasMapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)]


/-- The already constructed forward and reverse maps are inverse in retained degrees. -/
def negativeDegreeIso (n : ℕ) :
    (mapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)).X
      (-(n : ℤ)) ≅
    ((mapBifunctor K L F (down ℕ)).extend embeddingDownNat).X (-(n : ℤ)) where
  hom := forwardDegree F K L n
  inv := reverseDegree F K L n
  hom_inv_id := forwardDegree_reverseDegree F K L n
  inv_hom_id := reverseDegree_forwardDegree F K L n

/-- Every integer degree, including the actual zero objects in positive degrees. -/
def degreeIso (i : ℤ) :
    (mapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)).X i ≅
      ((mapBifunctor K L F (down ℕ)).extend embeddingDownNat).X i := by
  by_cases hi : i ≤ 0
  · have hi' : i = -(((-i).toNat : ℕ) : ℤ) := by omega
    rw [hi']
    exact negativeDegreeIso F K L (-i).toNat
  · exact (isZero_total_positive F K L i (by omega)).iso
      (CochainComplex.isZero_of_isStrictlyLE
        ((mapBifunctor K L F (down ℕ)).extend embeddingDownNat) 0 i (by omega))

/-- The true 0→1 boundary and all positive successor squares commute because
the target is the native zero term, not because the integer shape lacks an arrow. -/
theorem degreeIso_comm_nonnegative (i j : ℤ) (hi : 0 ≤ i) (hij : (up ℤ).Rel i j) :
    (degreeIso F K L i).hom ≫
        ((mapBifunctor K L F (down ℕ)).extend embeddingDownNat).d i j =
      (mapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)).d
        i j ≫ (degreeIso F K L j).hom := by
  have hj : 0 < j := by simp only [up_Rel] at hij; omega
  exact (CochainComplex.isZero_of_isStrictlyLE
    ((mapBifunctor K L F (down ℕ)).extend embeddingDownNat) 0 j hj).eq_of_tgt _ _

end HomologicalComplex.DownNatTensor
