/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import StacksFrontier.RingTheory.Norm.BaseChangeProduct

/-!
# Norms under an actual split-algebra equivalence

After base change splitting a finite free algebra as a product of copies of the base,
its determinant norm is the product of the component evaluations.
-/

@[expose] public noncomputable section

open scoped TensorProduct
namespace Algebra

variable {k A R : Type*} [CommRing k] [CommRing A] [CommRing R]
  [Algebra k A] [Algebra k R] [Module.Free k A] [Module.Finite k A]
  {I : Type*} [Fintype I]

/-- Determinant norm, after an actual splitting equivalence, is the sheet product. -/
theorem map_norm_eq_split_product (e : R ⊗[k] A ≃ₐ[R] (I → R)) (a : A) :
    algebraMap k R (Algebra.norm k a) = ∏ i, e (1 ⊗ₜ[k] a) i := by
  calc
    algebraMap k R (Algebra.norm k a) =
        Algebra.norm R (1 ⊗ₜ[k] a : R ⊗[k] A) :=
      (Stacks.Norm.norm_tmul_one a).symm
    _ = Algebra.norm R (e (1 ⊗ₜ[k] a)) :=
      (Algebra.norm_eq_of_algEquiv e _).symm
    _ = ∏ i, Algebra.norm R (e (1 ⊗ₜ[k] a) i) :=
      Stacks.Norm.norm_pi_apply (fun _ : I => R) _
    _ = ∏ i, e (1 ⊗ₜ[k] a) i := by simp only [Algebra.norm_self, MonoidHom.id_apply]

end Algebra
