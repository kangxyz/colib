/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Charpoly.Basic
public import Colib.RingTheory.Charpoly.TensorProduct

/-!
# Multiplication characteristic-polynomial powers over arbitrary fields

Choose a basis over the actual simple intermediate field. Its native coordinate
linear equivalence conjugates multiplication by the original element to the
finite product of multiplication by its original simple-field generator. The
characteristic polynomial is therefore the corresponding power of the minimal
polynomial. No polynomial-function extensionality, infinite-field hypothesis,
separability assumption or replacement field model is used.
-/

@[expose] public noncomputable section

namespace Algebra

/-- Actual multiplication has the minimal-polynomial power in every finite
field extension, including extensions of finite fields and inseparable ones. -/
theorem charpoly_lmul_eq_minpoly_pow_arbitrary
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] (a : L) :
    (lmul k L a).charpoly =
      (minpoly k a) ^ Module.finrank (IntermediateField.adjoin k {a}) L := by
  classical
  let F := IntermediateField.adjoin k {a}
  let x : F := IntermediateField.AdjoinSimple.gen k a
  let b := Module.finBasis F L
  let e0 := b.equivFun
  let e := e0.restrictScalars k
  have hmul (z : L) : a * z = x • z := by
    rw [Algebra.smul_def]
    rfl
  have hconj : e.conj (lmul k L a) =
      lmul k (Fin (Module.finrank F L) → F) (fun _ => x) := by
    apply LinearMap.ext
    intro y
    funext i
    change e0 (a * e0.symm y) i = x * y i
    rw [hmul, map_smul]
    simp only [e0.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (lmul k L a).charpoly = (e.conj (lmul k L a)).charpoly :=
      (e.charpoly_conj _).symm
    _ = (lmul k (Fin (Module.finrank F L) → F) (fun _ => x)).charpoly := by rw [hconj]
    _ = ∏ i : Fin (Module.finrank F L), (lmul k F x).charpoly :=
      charpoly_lmul_pi (fun _ : Fin (Module.finrank F L) => F) (fun _ => x)
    _ = (minpoly k a) ^ Module.finrank F L := by
      simp only [x, F, charpoly_lmul_adjoin_gen, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]

end Algebra
