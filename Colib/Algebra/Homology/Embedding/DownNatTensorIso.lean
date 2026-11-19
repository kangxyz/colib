/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.Embedding.DownNatTensorDegreeIso
public import Colib.Algebra.Homology.Embedding.DownNatTensorDifferential

/-! # Native signed tensor total versus the extended natural-chain total

The comparison uses the original coproduct degree maps and the original
extension identifications. No replacement complex or derived comparison is assumed.
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


/-- In retained degrees the integer family is exactly the original degree isomorphism. -/
theorem degreeIso_neg_nat (n : ℕ) :
    degreeIso F K L (-(n : ℤ)) = negativeDegreeIso F K L n := by
  cases n
  all_goals
    unfold degreeIso
    split
    · rfl
    · rename_i hn
      exact False.elim (hn (by omega))

/-- The actual degree isomorphisms commute with every differential allowed by the shape. -/
theorem degreeIso_comm (i j : ℤ) (hij : (up ℤ).Rel i j) :
    (degreeIso F K L i).hom ≫
        ((mapBifunctor K L F (down ℕ)).extend embeddingDownNat).d i j =
      (mapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ)).d
        i j ≫ (degreeIso F K L j).hom := by
  by_cases hi : 0 ≤ i
  · exact degreeIso_comm_nonnegative F K L i j hi hij
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -((n + 1 : ℕ) : ℤ) :=
      ⟨(-i - 1).toNat, by omega⟩
    have hj : j = -(n : ℤ) := by simp only [up_Rel] at hij; omega
    rw [hj]
    rw [degreeIso_neg_nat, degreeIso_neg_nat]
    exact forwardDegree_comm F K L n

/-- The signed integer tensor total is isomorphic to the native extension of
the original natural-chain tensor total. -/
def totalIso :
    mapBifunctor (K.extend embeddingDownNat) (L.extend embeddingDownNat) F (up ℤ) ≅
      (mapBifunctor K L F (down ℕ)).extend embeddingDownNat :=
  HomologicalComplex.Hom.isoOfComponents (degreeIso F K L) (degreeIso_comm F K L)

/-- The chain isomorphism retains the original forward coproduct map. -/
theorem totalIso_hom_f_neg (n : ℕ) :
    (totalIso F K L).hom.f (-(n : ℤ)) = forwardDegree F K L n := by
  change (degreeIso F K L (-(n : ℤ))).hom = _
  rw [degreeIso_neg_nat]
  rfl

/-- Its inverse retains the original reverse coproduct map. -/
theorem totalIso_inv_f_neg (n : ℕ) :
    (totalIso F K L).inv.f (-(n : ℤ)) = reverseDegree F K L n := by
  change (degreeIso F K L (-(n : ℤ))).inv = _
  rw [degreeIso_neg_nat]
  rfl

end HomologicalComplex.DownNatTensor
