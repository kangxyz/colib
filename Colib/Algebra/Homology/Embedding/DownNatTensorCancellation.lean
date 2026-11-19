/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Naturality in the inverse down-natural tensor comparison

This is the exact interchange of the two inverse extension arrows. It is
independent of totalization and does not assert that the degree maps already
form a chain isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape

namespace HomologicalComplex.DownNatTensor

variable {A B D : Type*} [Category* A] [Category* B] [Category* D]
  [HasZeroMorphisms A] [Limits.HasZeroObject A]
  [HasZeroMorphisms B] [Limits.HasZeroObject B]
  (F : A ⥤ B ⥤ D) (K : ChainComplex A ℕ) (L : ChainComplex B ℕ)

/-- The original reverse summand equals the reverse-order composite of the
inverse extension identifications, by naturality rather than definitional equality. -/
theorem inverse_extension_interchange (p q : ℕ) :
    (F.map (K.extendXIso embeddingDownNat (i := p) rfl).inv).app (L.X q) ≫
        (F.obj ((K.extend embeddingDownNat).X (-(p : ℤ)))).map
          (L.extendXIso embeddingDownNat (i := q) rfl).inv =
      (F.obj (K.X p)).map (L.extendXIso embeddingDownNat (i := q) rfl).inv ≫
        (F.map (K.extendXIso embeddingDownNat (i := p) rfl).inv).app
          ((L.extend embeddingDownNat).X (-(q : ℤ))) :=
  ((F.map (K.extendXIso embeddingDownNat (i := p) rfl).inv).naturality
    (L.extendXIso embeddingDownNat (i := q) rfl).inv).symm


/-- The actual retained bidegree comparison, before the total inclusion. -/
def retainedSummandIso (p q : ℕ) :
    (F.obj ((K.extend embeddingDownNat).X (-(p : ℤ)))).obj
        ((L.extend embeddingDownNat).X (-(q : ℤ))) ≅
      (F.obj (K.X p)).obj (L.X q) :=
  ((F.mapIso (K.extendXIso embeddingDownNat (i := p) rfl)).app
      ((L.extend embeddingDownNat).X (-(q : ℤ)))) ≪≫
    (F.obj (K.X p)).mapIso (L.extendXIso embeddingDownNat (i := q) rfl)

/-- The original order used in the reverse total inclusion. -/
def reverseSummand (p q : ℕ) :
    (F.obj (K.X p)).obj (L.X q) ⟶
      (F.obj ((K.extend embeddingDownNat).X (-(p : ℤ)))).obj
        ((L.extend embeddingDownNat).X (-(q : ℤ))) :=
  (F.map (K.extendXIso embeddingDownNat (i := p) rfl).inv).app (L.X q) ≫
    (F.obj ((K.extend embeddingDownNat).X (-(p : ℤ)))).map
      (L.extendXIso embeddingDownNat (i := q) rfl).inv

/-- Naturality identifies the original reverse arrow with the actual inverse. -/
theorem reverseSummand_eq_inv (p q : ℕ) :
    reverseSummand F K L p q = (retainedSummandIso F K L p q).inv :=
  inverse_extension_interchange F K L p q

/-- Cancellation on the original extended summand, without any extra sign. -/
theorem retainedSummand_hom_reverse (p q : ℕ) :
    (retainedSummandIso F K L p q).hom ≫ reverseSummand F K L p q = 𝟙 _ := by
  rw [reverseSummand_eq_inv]
  exact (retainedSummandIso F K L p q).hom_inv_id

/-- Cancellation on the original natural-chain summand. -/
theorem reverse_retainedSummand_hom (p q : ℕ) :
    reverseSummand F K L p q ≫ (retainedSummandIso F K L p q).hom = 𝟙 _ := by
  rw [reverseSummand_eq_inv]
  exact (retainedSummandIso F K L p q).inv_hom_id

end HomologicalComplex.DownNatTensor
