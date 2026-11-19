/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.Embedding.DownNatTensorDegree

/-! # Boundary differential terms for the original down-natural tensor comparison

The zero boundary is established on each original leg. In particular the
extended cochain differential from degree zero to degree one is zero, although
`up ℤ` itself has that arrow. No chain-comparison identity is assumed.
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

/-- The nonexistent original boundary out of degree zero stays zero after extension. -/
theorem extend_d_zero_to_one : (K.extend embeddingDownNat).d 0 1 = 0 := by
  apply K.extend_d_from_eq_zero embeddingDownNat 0 1 0 rfl
  simp

variable [HasMapBifunctor K L F (down ℕ)]
  [HasMapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)]

omit [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
  [HasMapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)] in
/-- The first leg of the ordinary chain total has no differential from index zero. -/
theorem original_d₁_boundary (q n : ℕ) :
    mapBifunctor.d₁ K L F (down ℕ) 0 q n = 0 := by
  apply mapBifunctor.d₁_eq_zero
  simp

omit [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
  [HasMapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)] in
/-- The second leg of the ordinary chain total has no differential from index zero. -/
theorem original_d₂_boundary (p n : ℕ) :
    mapBifunctor.d₂ K L F (down ℕ) p 0 n = 0 := by
  apply mapBifunctor.d₂_eq_zero
  simp

omit [HasZeroObject D] [HasMapBifunctor K L F (down ℕ)] in
/-- The apparently available first cochain boundary is zero on the actual extension. -/
theorem extended_d₁_boundary (j n : ℤ) :
    mapBifunctor.d₁ (K.extend embeddingDownNat) (L.extend embeddingDownNat) F
      (up ℤ) 0 j n = 0 := by
  rw [mapBifunctor.d₁_eq' _ _ F (up ℤ) (show (up ℤ).Rel 0 1 by simp) j n]
  simp [extend_d_zero_to_one]

omit [HasZeroObject D] [HasMapBifunctor K L F (down ℕ)] in
/-- The same vanishing holds for the actual second cochain boundary, including its sign. -/
theorem extended_d₂_boundary (i n : ℤ) :
    mapBifunctor.d₂ (K.extend embeddingDownNat) (L.extend embeddingDownNat) F
      (up ℤ) i 0 n = 0 := by
  rw [mapBifunctor.d₂_eq' _ _ F (up ℤ) i (show (up ℤ).Rel 0 1 by simp) n]
  simp [extend_d_zero_to_one]

omit [HasZeroObject D] [HasMapBifunctor K L F (down ℕ)] in
/-- On the first interior leg, the integer successor of `-(p+1)` is `-p`.
The actual extension differential is conjugate to the original chain differential. -/
theorem extended_d₁_interior (p q : ℕ) :
    mapBifunctor.d₁ (K.extend embeddingDownNat) (L.extend embeddingDownNat) F
      (up ℤ) (-((p + 1 : ℕ) : ℤ)) (-(q : ℤ)) (-((p + q : ℕ) : ℤ)) =
    (F.map ((K.extendXIso embeddingDownNat (i := p + 1) (i' := -((p + 1 : ℕ) : ℤ)) rfl).hom ≫
      K.d (p + 1) p ≫ (K.extendXIso embeddingDownNat (i := p) (i' := -(p : ℤ)) rfl).inv)).app _ ≫
      ιMapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)
        (-(p : ℤ)) (-(q : ℤ)) (-((p + q : ℕ) : ℤ))
          (by change -(p : ℤ) + -(q : ℤ) = -((p + q : ℕ) : ℤ); omega) := by
  rw [mapBifunctor.d₁_eq _ _ F (up ℤ)
    (show (up ℤ).Rel (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) by
      change -((p + 1 : ℕ) : ℤ) + 1 = -(p : ℤ); omega)
    (-(q : ℤ)) (-((p + q : ℕ) : ℤ))
          (by change -(p : ℤ) + -(q : ℤ) = -((p + q : ℕ) : ℤ); omega)]
  change (1 : ℤˣ) • _ = _
  rw [one_smul, extend_d_eq K embeddingDownNat
    (i := p + 1) (j := p) (i' := -((p + 1 : ℕ) : ℤ)) (j' := -(p : ℤ)) rfl rfl]

omit [HasZeroObject D] [HasMapBifunctor K L F (down ℕ)] in
/-- On the second interior leg the sign is exactly the original `(-1)^p`,
not an extra sign from reversing the indices. -/
theorem extended_d₂_interior (p q : ℕ) :
    mapBifunctor.d₂ (K.extend embeddingDownNat) (L.extend embeddingDownNat) F
      (up ℤ) (-(p : ℤ)) (-((q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ)) =
    (down ℕ).ε p •
      ((F.obj ((K.extend embeddingDownNat).X (-(p : ℤ)))).map
        ((L.extendXIso embeddingDownNat (i := q + 1) (i' := -((q + 1 : ℕ) : ℤ)) rfl).hom ≫
          L.d (q + 1) q ≫ (L.extendXIso embeddingDownNat (i := q) (i' := -(q : ℤ)) rfl).inv) ≫
        ιMapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)
          (-(p : ℤ)) (-(q : ℤ)) (-((p + q : ℕ) : ℤ))
          (by change -(p : ℤ) + -(q : ℤ) = -((p + q : ℕ) : ℤ); omega)) := by
  rw [mapBifunctor.d₂_eq _ _ F (up ℤ) (-(p : ℤ))
    (show (up ℤ).Rel (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) by
      change -((q + 1 : ℕ) : ℤ) + 1 = -(q : ℤ); omega)
    (-((p + q : ℕ) : ℤ))
          (by change -(p : ℤ) + -(q : ℤ) = -((p + q : ℕ) : ℤ); omega)]
  change (up ℤ).ε (-(p : ℤ)) • _ = _
  rw [sign_neg_nat, extend_d_eq L embeddingDownNat
    (i := q + 1) (j := q) (i' := -((q + 1 : ℕ) : ℤ)) (j' := -(q : ℤ)) rfl rfl]

end HomologicalComplex.DownNatTensor
