/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicTopology.DoldKan.CochainRepresentative
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Homotopies for the shifted good truncation

A cochain homotopy out of a complex supported in nonpositive degrees lifts to
the good truncation of the target. Below degree zero the inclusion is an
isomorphism. At the boundary the source of the homotopy component is zero.
This gives a homotopy between the chain maps selected by the strict-map
equivalence for the shifted simplicial representative.
-/

@[expose] public noncomputable section

open CategoryTheory Limits HomologicalComplex ComplexShape

universe v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

private theorem isIso_ιTruncLE_f_of_neg (T : CochainComplex A ℤ) (j : ℤ) (hj : j < 0) :
    IsIso ((HomologicalComplex.ιTruncLE T (embeddingUpIntLE 0)).f j) := by
  let e := embeddingUpIntLE 0
  obtain ⟨n, hn⟩ : ∃ n : ℕ, e.f n = j := by
    by_contra! h
    have := (notMem_range_embeddingUpIntLE_iff 0 j).1 h
    omega
  have hn₀ : ¬ e.BoundaryLE n := by
    rw [boundaryLE_embeddingUpIntLE_iff]
    rintro rfl
    have : j = 0 := by simpa [e] using hn.symm
    omega
  have : IsIso ((T.op.restrictionToTruncGE' e.op).f n) :=
    T.op.isIso_restrictionToTruncGE' e.op n (by simpa using hn₀)
  have : IsIso ((T.op.πTruncGE e.op).f j) := by
    change IsIso ((e.op.liftExtend (T.op.restrictionToTruncGE' e.op)
      (T.op.restrictionToTruncGE'_hasLift e.op)).f j)
    exact (e.op.isIso_liftExtend_f_iff _ _ hn).2 inferInstance
  change IsIso (((T.op.πTruncGE e.op).f j).unop)
  infer_instance

private def homotopyOfCompιTruncLE {S T : CochainComplex A ℤ} [S.IsStrictlyLE 0]
    {f g : S ⟶ HomologicalComplex.truncLE T (embeddingUpIntLE 0)}
    (h : Homotopy (f ≫ HomologicalComplex.ιTruncLE T (embeddingUpIntLE 0))
      (g ≫ HomologicalComplex.ιTruncLE T (embeddingUpIntLE 0))) : Homotopy f g := by
  let ι := HomologicalComplex.ιTruncLE T (embeddingUpIntLE 0)
  let hom (i j : ℤ) : S.X i ⟶ (HomologicalComplex.truncLE T (embeddingUpIntLE 0)).X j :=
    if hj : j < 0 then
      letI : IsIso (ι.f j) := isIso_ιTruncLE_f_of_neg T j hj
      h.hom i j ≫ inv (ι.f j)
    else 0
  have hhom (i j : ℤ) : hom i j ≫ ι.f j = h.hom i j := by
    by_cases hj : j < 0
    · let : IsIso (ι.f j) := isIso_ιTruncLE_f_of_neg T j hj
      simp only [hom, dite_eq_left hj, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    · simp only [hom, dite_eq_right hj, zero_comp]
      by_cases hij : (ComplexShape.up ℤ).Rel j i
      · change j + 1 = i at hij
        exact (S.isZero_of_isStrictlyLE 0 i (by omega)).eq_of_src _ _
      · exact (h.zero i j hij).symm
  refine { hom := hom, zero := ?_, comm := ?_ }
  · intro i j hij
    have : Mono (ι.f j) := inferInstance
    apply (cancel_mono (ι.f j)).1
    rw [hhom, zero_comp]
    exact h.zero i j hij
  · intro i
    have : Mono (ι.f i) := inferInstance
    apply (cancel_mono (ι.f i)).1
    simp only [Preadditive.add_comp, ← dNext_comp_right, ← prevD_comp_right, hhom]
    exact h.comm i

variable (A)

private theorem shiftedNonpositiveChainsHomEquiv_symm_apply (p : ℤ) (K : CochainComplex A ℤ)
    (P : ChainComplex A ℕ) (f : P ⟶ (shiftedNonpositiveChains A p).obj K) :
    (shiftedNonpositiveChainsHomEquiv A p K P).symm f =
      extendMap f (embeddingUpIntLE 0) ≫
        ((K⟦p⟧).truncLEIso (embeddingUpIntLE 0)).inv ≫
          HomologicalComplex.ιTruncLE (K⟦p⟧) (embeddingUpIntLE 0) :=
  rfl

/-- Good truncation and reindexing take a cochain homotopy to a homotopy
between the chain maps corresponding under the chosen strict-map equivalence. -/
@[no_expose]
def shiftedNonpositiveChainsHomEquivHomotopy (p : ℤ) (K : CochainComplex A ℤ)
    (P : ChainComplex A ℕ) {f g : P.extend (embeddingUpIntLE 0) ⟶ K⟦p⟧}
    (h : Homotopy f g) :
    Homotopy (shiftedNonpositiveChainsHomEquiv A p K P f)
      (shiftedNonpositiveChainsHomEquiv A p K P g) := by
  let e := embeddingUpIntLE 0
  let T := K⟦p⟧
  let E : (P.extend e ⟶ T) ≃ (P ⟶ T.truncLE' e) :=
    shiftedNonpositiveChainsHomEquiv A p K P
  let c := T.truncLEIso e
  let ι := HomologicalComplex.ιTruncLE T e
  have factor (k : P.extend e ⟶ T) : (extendMap (E k) e ≫ c.inv) ≫ ι = k :=
    (Category.assoc _ _ _).trans
      ((shiftedNonpositiveChainsHomEquiv_symm_apply A p K P (E k)).symm.trans
        (E.symm_apply_apply k))
  have h' : Homotopy ((extendMap (E f) e ≫ c.inv) ≫ ι)
      ((extendMap (E g) e ≫ c.inv) ≫ ι) := by
    rw [factor f, factor g]
    exact h
  have h'' := (homotopyOfCompιTruncLE h').compRight c.hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h''
  exact (Homotopy.extendEquiv e).symm h''

end CochainComplex
