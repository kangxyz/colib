/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.Embedding.DownNatTensorBoundary
public import Colib.Algebra.Homology.Embedding.DownNatTensorCancellation

/-! # Original summand differential compatibility

The first interior leg is compared using the original differential and
extension identifications. Full total-chain compatibility is not yet asserted.
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


/-- The first interior leg commutes with the actual forward total-degree map. -/
theorem extended_d₁_forwardDegree (p q : ℕ) :
    mapBifunctor.d₁ (K.extend embeddingDownNat) (L.extend embeddingDownNat) F
        (up ℤ) (-((p + 1 : ℕ) : ℤ)) (-(q : ℤ)) (-((p + q : ℕ) : ℤ)) ≫
      forwardDegree F K L (p + q) =
    (retainedSummandIso F K L (p + 1) q).hom ≫
      mapBifunctor.d₁ K L F (down ℕ) (p + 1) q (p + q) ≫
        ((mapBifunctor K L F (down ℕ)).extendXIso embeddingDownNat
          (i := p + q) (i' := -((p + q : ℕ) : ℤ)) rfl).inv := by
  rw [extended_d₁_interior, Category.assoc, inclusion_forwardDegree,
    component_neg_nat F K L p q (p + q) rfl]
  rw [mapBifunctor.d₁_eq K L F (down ℕ)
    (show (down ℕ).Rel (p + 1) p by simp) q (p + q) (by rfl)]
  change _ = (retainedSummandIso F K L (p + 1) q).hom ≫ ((1 : ℤˣ) • _) ≫ _
  rw [one_smul]
  simp [retainedComponent, retainedSummandIso, Functor.map_comp, Category.assoc]


/-- The signed second leg commutes with the actual forward degree map, with
exactly the original sign at the first natural index. -/
theorem extended_d₂_forwardDegree (p q : ℕ) :
    mapBifunctor.d₂ (K.extend embeddingDownNat) (L.extend embeddingDownNat) F
        (up ℤ) (-(p : ℤ)) (-((q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ)) ≫
      forwardDegree F K L (p + q) =
    (retainedSummandIso F K L p (q + 1)).hom ≫
      mapBifunctor.d₂ K L F (down ℕ) p (q + 1) (p + q) ≫
        ((mapBifunctor K L F (down ℕ)).extendXIso embeddingDownNat
          (i := p + q) (i' := -((p + q : ℕ) : ℤ)) rfl).inv := by
  rw [extended_d₂_interior, Linear.units_smul_comp, Category.assoc,
    inclusion_forwardDegree, component_neg_nat F K L p q (p + q) rfl]
  rw [mapBifunctor.d₂_eq K L F (down ℕ) p
    (show (down ℕ).Rel (q + 1) q by simp) (p + q) (by rfl)]
  change _ = (retainedSummandIso F K L p (q + 1)).hom ≫
    ((down ℕ).ε p • _) ≫ _
  simp [retainedComponent, retainedSummandIso, Functor.map_comp, Category.assoc,
    Linear.units_smul_comp, Linear.comp_units_smul]

/-- The first-leg boundary comparison is between actual zero differentials. -/
theorem extended_d₁_forwardDegree_boundary (q n : ℕ) :
    mapBifunctor.d₁ (K.extend embeddingDownNat) (L.extend embeddingDownNat) F
        (up ℤ) 0 (-(q : ℤ)) (-(n : ℤ)) ≫ forwardDegree F K L n =
      (retainedSummandIso F K L 0 q).hom ≫
        mapBifunctor.d₁ K L F (down ℕ) 0 q n ≫
          ((mapBifunctor K L F (down ℕ)).extendXIso embeddingDownNat
            (i := n) (i' := -(n : ℤ)) rfl).inv := by
  simp only [extended_d₁_boundary, original_d₁_boundary, zero_comp, comp_zero]

/-- The signed second-leg boundary likewise compares the original zero arrows. -/
theorem extended_d₂_forwardDegree_boundary (p n : ℕ) :
    mapBifunctor.d₂ (K.extend embeddingDownNat) (L.extend embeddingDownNat) F
        (up ℤ) (-(p : ℤ)) 0 (-(n : ℤ)) ≫ forwardDegree F K L n =
      (retainedSummandIso F K L p 0).hom ≫
        mapBifunctor.d₂ K L F (down ℕ) p 0 n ≫
          ((mapBifunctor K L F (down ℕ)).extendXIso embeddingDownNat
            (i := n) (i' := -(n : ℤ)) rfl).inv := by
  simp only [extended_d₂_boundary, original_d₂_boundary, zero_comp, comp_zero]


/-- First-leg compatibility at every retained source bidegree, including p=0. -/
theorem extended_d₁_forwardDegree_of_sum (p q n : ℕ) (h : p + q = n + 1) :
    mapBifunctor.d₁ (K.extend embeddingDownNat) (L.extend embeddingDownNat) F
        (up ℤ) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) ≫ forwardDegree F K L n =
      (retainedSummandIso F K L p q).hom ≫
        mapBifunctor.d₁ K L F (down ℕ) p q n ≫
          ((mapBifunctor K L F (down ℕ)).extendXIso embeddingDownNat
            (i := n) (i' := -(n : ℤ)) rfl).inv := by
  cases p with
  | zero => exact extended_d₁_forwardDegree_boundary F K L q n
  | succ p =>
    have hn : n = p + q := by omega
    subst n
    exact extended_d₁_forwardDegree F K L p q

/-- Second-leg compatibility at every retained source bidegree, including q=0. -/
theorem extended_d₂_forwardDegree_of_sum (p q n : ℕ) (h : p + q = n + 1) :
    mapBifunctor.d₂ (K.extend embeddingDownNat) (L.extend embeddingDownNat) F
        (up ℤ) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) ≫ forwardDegree F K L n =
      (retainedSummandIso F K L p q).hom ≫
        mapBifunctor.d₂ K L F (down ℕ) p q n ≫
          ((mapBifunctor K L F (down ℕ)).extendXIso embeddingDownNat
            (i := n) (i' := -(n : ℤ)) rfl).inv := by
  cases q with
  | zero => exact extended_d₂_forwardDegree_boundary F K L p n
  | succ q =>
    have hn : n = p + q := by omega
    subst n
    exact extended_d₂_forwardDegree F K L p q

/-- The two actual total-differential contributions commute together on every
retained summand. Both zero-leg cases are included by the preceding case splits. -/
theorem extended_totalLegs_forwardDegree (p q n : ℕ) (h : p + q = n + 1) :
    (mapBifunctor.d₁ (K.extend embeddingDownNat) (L.extend embeddingDownNat) F
        (up ℤ) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) +
      mapBifunctor.d₂ (K.extend embeddingDownNat) (L.extend embeddingDownNat) F
        (up ℤ) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ))) ≫ forwardDegree F K L n =
      (retainedSummandIso F K L p q).hom ≫
        (mapBifunctor.d₁ K L F (down ℕ) p q n +
          mapBifunctor.d₂ K L F (down ℕ) p q n) ≫
          ((mapBifunctor K L F (down ℕ)).extendXIso embeddingDownNat
            (i := n) (i' := -(n : ℤ)) rfl).inv := by
  simpa only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc] using
    congrArg₂ (fun f g => f + g)
      (extended_d₁_forwardDegree_of_sum F K L p q n h)
      (extended_d₂_forwardDegree_of_sum F K L p q n h)


/-- The actual coproduct inclusion turns the assembled leg comparison into
compatibility with both original total differentials. -/
theorem retained_inclusion_total_d (p q n : ℕ) (h : p + q = n + 1) :
    ιMapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)
        (-(p : ℤ)) (-(q : ℤ)) (-((n + 1 : ℕ) : ℤ))
          (retained_total_index p q (n + 1) h) ≫
      (mapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)).d
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫ forwardDegree F K L n =
      (retainedSummandIso F K L p q).hom ≫
        ιMapBifunctor K L F (down ℕ) p q (n + 1) h ≫
          (mapBifunctor K L F (down ℕ)).d (n + 1) n ≫
            ((mapBifunctor K L F (down ℕ)).extendXIso embeddingDownNat
              (i := n) (i' := -(n : ℤ)) rfl).inv := by
  simpa only [mapBifunctor.d_eq, Preadditive.comp_add, Preadditive.add_comp,
    Category.assoc, mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc] using
    extended_totalLegs_forwardDegree F K L p q n h

omit [HasZeroObject A] [HasZeroObject B]
  [HasMapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)] in
/-- The inverse native extension identification intertwines the actual
natural total differential and its negative-degree extension. -/
theorem total_extension_inv_d (n : ℕ) :
    ((mapBifunctor K L F (down ℕ)).extendXIso embeddingDownNat
        (i := n + 1) (i' := -((n + 1 : ℕ) : ℤ)) rfl).inv ≫
      ((mapBifunctor K L F (down ℕ)).extend embeddingDownNat).d
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (mapBifunctor K L F (down ℕ)).d (n + 1) n ≫
        ((mapBifunctor K L F (down ℕ)).extendXIso embeddingDownNat
          (i := n) (i' := -(n : ℤ)) rfl).inv := by
  rw [extend_d_eq (mapBifunctor K L F (down ℕ)) embeddingDownNat
    (i := n + 1) (j := n) (i' := -((n + 1 : ℕ) : ℤ)) (j' := -(n : ℤ)) rfl rfl]
  simp only [Iso.inv_hom_id_assoc]


/-- The full negative-successor differential square follows by extensionality
on the original integer antidiagonal, including all zero-source summands. -/
theorem forwardDegree_comm (n : ℕ) :
    forwardDegree F K L (n + 1) ≫
        ((mapBifunctor K L F (down ℕ)).extend embeddingDownNat).d
          (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (mapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)).d
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫ forwardDegree F K L n := by
  apply mapBifunctor.hom_ext
  intro i j hij
  by_cases hi : i ≤ 0
  · by_cases hj : j ≤ 0
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨q, rfl⟩ : ∃ q : ℕ, j = -(q : ℤ) := ⟨(-j).toNat, by omega⟩
      have h : p + q = n + 1 := by dsimp at hij; omega
      rw [← Category.assoc, inclusion_forwardDegree,
        component_neg_nat F K L p q (n + 1) h]
      calc
        _ = (retainedSummandIso F K L p q).hom ≫
            ιMapBifunctor K L F (down ℕ) p q (n + 1) h ≫
              (mapBifunctor K L F (down ℕ)).d (n + 1) n ≫
                ((mapBifunctor K L F (down ℕ)).extendXIso embeddingDownNat
                  (i := n) (i' := -(n : ℤ)) rfl).inv := by
          simp only [retainedComponent, Category.assoc, total_extension_inv_d]
          simp [retainedSummandIso, Category.assoc]
        _ = _ := (retained_inclusion_total_d F K L p q n h).symm
    · exact (isZero_summand F K L i j (Or.inr (by omega))).eq_of_src _ _
  · exact (isZero_summand F K L i j (Or.inl (by omega))).eq_of_src _ _

end HomologicalComplex.DownNatTensor
