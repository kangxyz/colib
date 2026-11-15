/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz

Adapted from the TensorExtension section of
StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/
SymmetricPowerVanishing/HomologyVanishing.lean.
The categorical comparison proof and sign computations below follow that upstream source;
this adaptation removes its ModuleCat specialization.
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Tensor products and extension from chain to cochain complexes

Extension from nonnegative chains to nonpositive cochains preserves the actual total tensor
product. This is an ordinary complex comparison, not a derived tensor statement.

The tensor objects are direct-sum totalizations. Small coproducts suffice for their existence.
No preservation of coproducts by tensor is required for this binary comparison: its proof uses
only the universal property of each totalization, additivity, and preservation of zero objects
by left and right tensoring (the latter follows from additivity). In particular, associators of
the monoidal structure on complexes, which require preservation of the relevant coproducts,
are not used here.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory

namespace HomologicalComplex.TensorNegExtend

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{0} C]

/-- A chain complex indexed by `ℕ`, viewed as a cochain complex indexed by `ℤ` concentrated in
nonpositive degrees, with `K_p` in degree `-p`. -/
abbrev negExtend (K : ChainComplex C ℕ) :=
  K.extend ComplexShape.embeddingDownNat
/-- The term of `negExtend K` in degree `-p` is `K_p`. -/
abbrev negExtendIso (K : ChainComplex C ℕ) (p : ℕ) :
    (negExtend K).X (-(p : ℤ)) ≅ K.X p :=
  K.extendXIso ComplexShape.embeddingDownNat rfl
/-- The comparison map from the degree `n` term of `K ⊗ L` to the degree `-n` term of
`negExtend K ⊗ negExtend L`. -/
def tensorNegExtendHom
    (K L : ChainComplex C ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj K L).X n ⟶
      (HomologicalComplex.tensorObj (negExtend K) (negExtend L)).X (-(n : ℤ)) :=
  mapBifunctorDesc (fun p q hpq =>
    ((negExtendIso K p).inv ⊗ₘ (negExtendIso L q).inv) ≫
      ιTensorObj (negExtend K) (negExtend L) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ))
        (by change _ + _ = _ at hpq; omega))
/-- The comparison map from the degree `-n` term of `negExtend K ⊗ negExtend L` to the degree
`n` term of `K ⊗ L`. -/
def tensorNegExtendInv
    (K L : ChainComplex C ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj (negExtend K) (negExtend L)).X (-(n : ℤ)) ⟶
      (HomologicalComplex.tensorObj K L).X n :=
  mapBifunctorDesc (fun p q hpq =>
    if hp : p ≤ 0 then if hq : q ≤ 0 then
      ((K.extendXIso ComplexShape.embeddingDownNat
          (i := (-p).toNat) (by change -(((-p).toNat : ℕ) : ℤ) = p; omega)).hom ⊗ₘ
        (L.extendXIso ComplexShape.embeddingDownNat
          (i := (-q).toNat) (by change -(((-q).toNat : ℕ) : ℤ) = q; omega)).hom) ≫
        ιTensorObj K L (-p).toNat (-q).toNat n (by change _ + _ = _ at hpq; omega)
    else 0 else 0)

/-- The inclusion of `K_p ⊗ L_q` into `(K ⊗ L)_n`, precomposed with the identifications of the
terms of the extended complexes, does not depend on the indices `pp`, `qq` used to name them. -/
lemma tensorNegExtendInv_term
    (K L : ChainComplex C ℕ) (p q n pp qq : ℕ)
    (hp : ComplexShape.embeddingDownNat.f pp = -(p : ℤ))
    (hq : ComplexShape.embeddingDownNat.f qq = -(q : ℤ))
    (h : p + q = n) (hh : pp + qq = n) :
    ((K.extendXIso ComplexShape.embeddingDownNat hp).hom ⊗ₘ
      (L.extendXIso ComplexShape.embeddingDownNat hq).hom) ≫ ιTensorObj K L pp qq n hh =
    ((negExtendIso K p).hom ⊗ₘ (negExtendIso L q).hom) ≫ ιTensorObj K L p q n h := by
  have hpp : pp = p := by change -(pp : ℤ) = -(p : ℤ) at hp; omega
  have hqq : qq = q := by change -(qq : ℤ) = -(q : ℤ) at hq; omega
  subst pp qq
  rfl

/-- `tensorNegExtendInv` sends the summand in degrees `(-p, -q)` to the summand `K_p ⊗ L_q`. -/
lemma tensorNegExtendInv_ι
    (K L : ChainComplex C ℕ) (p q n : ℕ) (h : p + q = n) :
    ιTensorObj (negExtend K) (negExtend L) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ))
      (by omega) ≫ tensorNegExtendInv K L n =
    ((negExtendIso K p).hom ⊗ₘ (negExtendIso L q).hom) ≫ ιTensorObj K L p q n h := by
  dsimp only [tensorNegExtendInv]
  rw [ι_mapBifunctorDesc]
  simp only [dite_eq_left (show -(p : ℤ) ≤ 0 by omega),
    dite_eq_left (show -(q : ℤ) ≤ 0 by omega)]
  exact tensorNegExtendInv_term K L p q n _ _ _ _ h _

/-- `tensorNegExtendInv` is a left inverse of `tensorNegExtendHom`. -/
lemma tensorNegExtendHom_inv
    (K L : ChainComplex C ℕ) (n : ℕ) :
    tensorNegExtendHom K L n ≫ tensorNegExtendInv K L n = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  simp only [tensorNegExtendHom, ι_mapBifunctorDesc_assoc, Category.assoc,
    tensorNegExtendInv_ι K L p q n hpq, tensorHom_comp_tensorHom_assoc,
    Iso.inv_hom_id, id_tensorHom_id, Category.id_comp, Category.comp_id]

/-- `tensorNegExtendInv` is a right inverse of `tensorNegExtendHom`. -/
lemma tensorNegExtendInv_hom
    (K L : ChainComplex C ℕ) (n : ℕ) :
    tensorNegExtendInv K L n ≫ tensorNegExtendHom K L n = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  by_cases hp : p ≤ 0
  · by_cases hq : q ≤ 0
    · obtain ⟨p, rfl⟩ : ∃ p' : ℕ, p = -(p' : ℤ) := ⟨(-p).toNat, by omega⟩
      obtain ⟨q, rfl⟩ : ∃ q' : ℕ, q = -(q' : ℤ) := ⟨(-q).toNat, by omega⟩
      have hn : p + q = n := by change _ + _ = _ at hpq; omega
      rw [← Category.assoc, tensorNegExtendInv_ι K L p q n hn]
      simp only [tensorNegExtendHom, Category.assoc, ι_mapBifunctorDesc,
        tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id, id_tensorHom_id,
        Category.id_comp, Category.comp_id]
    · have hz : IsZero ((negExtend K).X p ⊗ (negExtend L).X q) :=
        (tensorLeft _).map_isZero (L.isZero_extend_X ComplexShape.embeddingDownNat q
          (by intro i; change -(i : ℤ) ≠ q; omega))
      exact hz.eq_of_src _ _
  · have hz : IsZero ((negExtend K).X p ⊗ (negExtend L).X q) :=
      (tensorRight _).map_isZero (K.isZero_extend_X ComplexShape.embeddingDownNat p
        (by intro i; change -(i : ℤ) ≠ p; omega))
    exact hz.eq_of_src _ _

/-- The isomorphism between the degree `n` term of `K ⊗ L` and the degree `-n` term of
`negExtend K ⊗ negExtend L`. -/
def tensorNegExtendIso
    (K L : ChainComplex C ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj K L).X n ≅
      (HomologicalComplex.tensorObj (negExtend K) (negExtend L)).X (-(n : ℤ)) where
  hom := tensorNegExtendHom K L n
  inv := tensorNegExtendInv K L n
  hom_inv_id := tensorNegExtendHom_inv K L n
  inv_hom_id := tensorNegExtendInv_hom K L n

/-- The sign `ε₁` of the tensor product of complexes of a shape with itself is `1`. -/
lemma tensor_epsilon₁ {I : Type*} [AddMonoid I]
    (c : ComplexShape I) [c.TensorSigns] (p q : I) :
    ComplexShape.ε₁ c c c (p, q) = 1 := rfl

/-- The sign `ε₂` of the tensor product of complexes of a shape with itself at `(p, q)` is
`ε p`. -/
lemma tensor_epsilon₂ {I : Type*} [AddMonoid I]
    (c : ComplexShape I) [c.TensorSigns] (p q : I) :
    ComplexShape.ε₂ c c c (p, q) = c.ε p := rfl

/-- For cochain complexes indexed by `ℤ`, the sign `ε` at `-p` is `(-1)ᵖ`. -/
lemma tensor_epsilon_neg (p : ℕ) :
    (ComplexShape.up ℤ).ε (-(p : ℤ)) = (-1 : ℤˣ) ^ p := by
  change (-(p : ℤ)).negOnePow = _
  rw [Int.negOnePow_neg, Int.negOnePow_def, zpow_natCast]

/-- `tensorNegExtendHom` is compatible with the component `d₁` of the differential coming from
the first factor. -/
lemma tensorNegExtendHom_d₁
    (K L : ChainComplex C ℕ) (p q n : ℕ)
    (h : p + q = n + 1) :
    mapBifunctor.d₁ K L (curriedTensor _) (ComplexShape.down ℕ) p q n ≫
        tensorNegExtendHom K L n =
      ((negExtendIso K p).inv ⊗ₘ (negExtendIso L q).inv) ≫
        mapBifunctor.d₁ (negExtend K) (negExtend L) (curriedTensor _)
          (ComplexShape.up ℤ) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) := by
  cases p with
  | zero =>
      rw [mapBifunctor.d₁_eq_zero K L _ _ _ _ _ (by simp), zero_comp]
      rw [mapBifunctor.d₁_eq _ _ _ _ (i₁' := 1) (by simp) _ _ (by dsimp; omega)]
      simp only [Nat.cast_zero, neg_zero]
      rw [K.extend_d_from_eq_zero ComplexShape.embeddingDownNat (-((0 : ℕ) : ℤ)) 1 0 rfl (by simp)]
      simp
  | succ p =>
      rw [mapBifunctor.d₁_eq K L _ _ (i₁' := p) rfl _ _ (by dsimp; omega),
        mapBifunctor.d₁_eq _ _ _ _ (i₁' := -(p : ℤ)) (by change _ + 1 = _; push_cast; omega)
          _ _ (by dsimp; omega)]
      simp only [tensor_epsilon₁, one_smul, Category.assoc,
        tensorNegExtendHom, ι_mapBifunctorDesc]
      change (K.d (p + 1) p ▷ L.X q) ≫
          ((negExtendIso K p).inv ⊗ₘ (negExtendIso L q).inv) ≫ _ =
        ((negExtendIso K (p + 1)).inv ⊗ₘ (negExtendIso L q).inv) ≫
          ((negExtend K).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ▷ (negExtend L).X (-(q : ℤ))) ≫ _
      rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc]
      rw [K.extend_d_eq ComplexShape.embeddingDownNat (i := p + 1) (j := p)
        (i' := -((p + 1 : ℕ) : ℤ)) (j' := -(p : ℤ)) rfl rfl]
      simp [negExtendIso]

/-- `tensorNegExtendHom` is compatible with the component `d₂` of the differential coming from
the second factor. -/
lemma tensorNegExtendHom_d₂
    (K L : ChainComplex C ℕ) (p q n : ℕ)
    (h : p + q = n + 1) :
    mapBifunctor.d₂ K L (curriedTensor _) (ComplexShape.down ℕ) p q n ≫
        tensorNegExtendHom K L n =
      ((negExtendIso K p).inv ⊗ₘ (negExtendIso L q).inv) ≫
        mapBifunctor.d₂ (negExtend K) (negExtend L) (curriedTensor _)
          (ComplexShape.up ℤ) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) := by
  cases q with
  | zero =>
      rw [mapBifunctor.d₂_eq_zero K L _ _ _ _ _ (by simp), zero_comp]
      rw [mapBifunctor.d₂_eq _ _ _ _ _ (i₂' := 1) (by simp) _ (by dsimp; omega)]
      simp only [Nat.cast_zero, neg_zero]
      rw [L.extend_d_from_eq_zero ComplexShape.embeddingDownNat (-((0 : ℕ) : ℤ)) 1 0 rfl (by simp)]
      simp
  | succ q =>
      rw [mapBifunctor.d₂_eq K L _ _ _ (i₂' := q) rfl _ (by dsimp; omega),
        mapBifunctor.d₂_eq _ _ _ _ _ (i₂' := -(q : ℤ)) (by change _ + 1 = _; push_cast; omega)
          _ (by dsimp; omega)]
      simp only [tensor_epsilon₂, tensor_epsilon_neg, ComplexShape.ε_down_ℕ, Linear.units_smul_comp,
        Linear.comp_units_smul, Category.assoc, tensorNegExtendHom, ι_mapBifunctorDesc]
      congr 1
      change (K.X p ◁ L.d (q + 1) q) ≫
          ((negExtendIso K p).inv ⊗ₘ (negExtendIso L q).inv) ≫ _ =
        ((negExtendIso K p).inv ⊗ₘ (negExtendIso L (q + 1)).inv) ≫
          ((negExtend K).X (-(p : ℤ)) ◁ (negExtend L).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ))) ≫ _
      rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc]
      rw [L.extend_d_eq ComplexShape.embeddingDownNat (i := q + 1) (j := q)
        (i' := -((q + 1 : ℕ) : ℤ)) (j' := -(q : ℤ)) rfl rfl]
      simp [negExtendIso]

/-- `tensorNegExtendHom` commutes with the differentials of `K ⊗ L` and of
`negExtend K ⊗ negExtend L`. -/
lemma tensorNegExtendHom_comm
    (K L : ChainComplex C ℕ) (n : ℕ) :
    tensorNegExtendHom K L (n + 1) ≫
      (HomologicalComplex.tensorObj (negExtend K) (negExtend L)).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
    (HomologicalComplex.tensorObj K L).d (n + 1) n ≫ tensorNegExtendHom K L n := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  rw [← Category.assoc]
  simp only [tensorNegExtendHom, ι_mapBifunctorDesc]
  simp only [mapBifunctor.d_eq, Category.assoc, Preadditive.comp_add, Preadditive.add_comp,
    mapBifunctor.ι_D₁, mapBifunctor.ι_D₂, mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc]
  exact congrArg₂ (· + ·) (tensorNegExtendHom_d₁ K L p q n hpq).symm
    (tensorNegExtendHom_d₂ K L p q n hpq).symm

/-- The tensor product `K ⊗ L` of chain complexes indexed by `ℕ` is isomorphic to the restriction
to nonpositive degrees of `negExtend K ⊗ negExtend L`. -/
def tensorNegExtendComplexIso
    (K L : ChainComplex C ℕ) :
    HomologicalComplex.tensorObj K L ≅
      (HomologicalComplex.tensorObj (negExtend K) (negExtend L)).restriction
        ComplexShape.embeddingDownNat :=
  Hom.isoOfComponents (fun n => tensorNegExtendIso K L n) (by
    intro i j hij
    have h : j + 1 = i := hij
    subst i
    exact tensorNegExtendHom_comm K L j)

/-- The tensor of two extensions has no terms in positive degrees. -/
lemma isZero_tensorNegExtend_X (K L : ChainComplex C ℕ) (i : ℤ) (hi : 0 < i) :
    IsZero ((HomologicalComplex.tensorObj (negExtend K) (negExtend L)).X i) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hz : IsZero ((negExtend K).X p ⊗ (negExtend L).X q) := by
    by_cases hp : 0 < p
    · exact (tensorRight _).map_isZero
        (K.isZero_extend_X ComplexShape.embeddingDownNat p
          (by intro n; change -(n : ℤ) ≠ p; omega))
    · exact (tensorLeft _).map_isZero
        (L.isZero_extend_X ComplexShape.embeddingDownNat q
          (by intro n; change -(n : ℤ) ≠ q; dsimp at hpq; omega))
  exact hz.eq_of_src _ _

/-- Extend the restricted tensor comparison along the actual shape embedding. -/
def tensorNegExtendMap (K L : ChainComplex C ℕ) :
    HomologicalComplex.tensorObj (negExtend K) (negExtend L) ⟶
      negExtend (HomologicalComplex.tensorObj K L) :=
  ComplexShape.embeddingDownNat.liftExtend (tensorNegExtendComplexIso K L).inv
    (fun _ h _ _ => h.false_of_isTruncLE.elim)

instance tensorNegExtendMap_isIso (K L : ChainComplex C ℕ) :
    IsIso (tensorNegExtendMap K L) := by
  have h (i : ℤ) : IsIso ((tensorNegExtendMap K L).f i) := by
    by_cases hi : ∃ n, ComplexShape.embeddingDownNat.f n = i
    · obtain ⟨n, hn⟩ := hi
      apply (ComplexShape.embeddingDownNat.isIso_liftExtend_f_iff
        (tensorNegExtendComplexIso K L).inv _ hn).2
      infer_instance
    · have hpos : 0 < i := by
        by_contra h
        apply hi
        exact ⟨(-i).toNat, by change -(((-i).toNat : ℕ) : ℤ) = i; omega⟩
      exact (isZero_tensorNegExtend_X K L i hpos).isIso
        ((HomologicalComplex.tensorObj K L).isZero_extend_X
          ComplexShape.embeddingDownNat i (by simpa using hi)) _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Extension from chains to nonpositive cochains preserves the actual total tensor. -/
def tensorNegExtendFullIso (K L : ChainComplex C ℕ) :
    HomologicalComplex.tensorObj (negExtend K) (negExtend L) ≅
      negExtend (HomologicalComplex.tensorObj K L) :=
  asIso (tensorNegExtendMap K L)

end HomologicalComplex.TensorNegExtend
