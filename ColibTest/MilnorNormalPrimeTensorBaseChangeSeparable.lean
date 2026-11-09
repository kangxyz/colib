/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeTensorBaseChange
import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeTensorBaseChangeSeparable

/-! Full native tensor-factor formulas, using only separability of the source extension. -/

noncomputable section

open Polynomial Module Stacks.Chow
open scoped TensorProduct

universe u v

variable {F K E : Type u} [Field F] [Field K] [Field E]
  [Algebra F K] [Algebra F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Normal F E]
  {ι : Type v} [Fintype ι] {D : ι → Type u}
  [∀ j, Field (D j)] [∀ j, Algebra K (D j)]

example
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) (j : ι) :
    Algebra.IsSeparable K (D j) :=
  isSeparable_of_tensorProductPiEquiv pb ε j

example
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j))
    (hp : Nat.Prime (finrank F E)) (j : ι) :
    finrank K (D j) = 1 ∨ finrank K (D j) = finrank F E :=
  finrank_eq_one_or_eq_of_tensorProductPiEquiv_of_normal_prime_of_separable pb ε hp j

example
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j))
    (hp : Nat.Prime (finrank F E)) (x : MilnorKRing E) :
    let : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    milnorKRingMap (algebraMap F K) (milnorKNormRing F E x) =
      ∑ j, milnorKNormRing K (D j)
        (milnorKRingMap ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) x) :=
  milnorKNormRing_map_eq_sum_tensorProductPiEquiv_of_normal_prime_of_separable pb ε hp x

example
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j))
    (hp : Nat.Prime (finrank F E)) :
    let : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    (milnorKRingMap (algebraMap F K)).toAddMonoidHom.comp (milnorKNormRing F E) =
      ∑ j, (milnorKNormRing K (D j)).comp
        (milnorKRingMap ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))).toAddMonoidHom :=
  milnorKNormRing_comp_map_eq_sum_tensorProductPiEquiv_of_normal_prime_of_separable pb ε hp

example
    (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j))
    (hp : Nat.Prime (finrank F E)) (n : ℕ) (x : MilnorKTheory E n) :
    let : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    milnorKTheoryMap (algebraMap F K) n (milnorKNorm F E n x) =
      ∑ j, milnorKNorm K (D j) n
        (milnorKTheoryMap ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) n x) :=
  milnorKNorm_map_eq_sum_tensorProductPiEquiv_of_normal_prime_of_separable pb ε hp n x

end
