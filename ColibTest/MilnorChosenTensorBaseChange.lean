/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenTensorBaseChange

noncomputable section

open Stacks.Chow
open scoped TensorProduct

universe u v

variable {F K E : Type u} [Field F] [Field K] [Field E]
  [Algebra F K] [Algebra F E] [FiniteDimensional F E] [CharZero F]
  {ι : Type v} [Fintype ι] {D : ι → Type u}
  [∀ j, Field (D j)] [∀ j, Algebra K (D j)]

/-- The caller may retain a prescribed source power basis, with no branch hypotheses. -/
example (pb : PowerBasis F E) (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j))
    (x : MilnorKRing E) :
    let _ : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    milnorKRingMap (algebraMap F K) (milnorKNormRing F E x) =
      ∑ j, milnorKNormRing K (D j)
        (milnorKRingMap ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) x) :=
  milnorKNormRing_map_eq_sum_tensorProductPiEquiv_of_powerBasis pb ε x

/-- An arbitrary finite source requires no supplied presentation or normality. -/
example (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) (x : MilnorKRing E) :
    let pb := Field.powerBasisOfFiniteOfSeparable F E
    let _ : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    milnorKRingMap (algebraMap F K) (milnorKNormRing F E x) =
      ∑ j, milnorKNormRing K (D j)
        (milnorKRingMap ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) x) :=
  milnorKNormRing_map_eq_sum_tensorProductPiEquiv ε x

/-- The presentation-free formula is equality of the actual whole-ring additive maps. -/
example (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) :
    let pb := Field.powerBasisOfFiniteOfSeparable F E
    let _ : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    (milnorKRingMap (algebraMap F K)).toAddMonoidHom.comp (milnorKNormRing F E) =
      ∑ j, (milnorKNormRing K (D j)).comp
        (milnorKRingMap ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))).toAddMonoidHom :=
  milnorKNormRing_comp_map_eq_sum_tensorProductPiEquiv ε

/-- Every homogeneous group uses the same original coordinate ring maps. -/
example (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) (n : ℕ) (x : MilnorKTheory E n) :
    let pb := Field.powerBasisOfFiniteOfSeparable F E
    let _ : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    milnorKTransport (algebraMap F K) n (milnorKNorm F E n x) =
      ∑ j, milnorKNorm K (D j) n
        (milnorKTransport ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) n x) :=
  milnorKNorm_map_eq_sum_tensorProductPiEquiv ε n x

/-- Equality of the native homogeneous additive maps needs no positive-degree condition. -/
example (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) (n : ℕ) :
    let pb := Field.powerBasisOfFiniteOfSeparable F E
    let _ : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    (milnorKTransport (algebraMap F K) n).comp (milnorKNorm F E n) =
      ∑ j, (milnorKNorm K (D j) n).comp
        (milnorKTransport ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) n) :=
  milnorKNorm_comp_map_eq_sum_tensorProductPiEquiv ε n

/-- Degree zero is a literal specialization, not an omitted boundary case. -/
example (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) (x : MilnorKTheory E 0) :
    let pb := Field.powerBasisOfFiniteOfSeparable F E
    let _ : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    milnorKTransport (algebraMap F K) 0 (milnorKNorm F E 0 x) =
      ∑ j, milnorKNorm K (D j) 0
        (milnorKTransport ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) 0 x) :=
  milnorKNorm_map_eq_sum_tensorProductPiEquiv ε 0 x

/-- Native tuple symbols use the actual coordinate images of every unit. -/
example (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) (n : ℕ) (a : Fin n → Eˣ) :
    let pb := Field.powerBasisOfFiniteOfSeparable F E
    let _ : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    milnorKTransport (algebraMap F K) n (milnorKNorm F E n (milnorKTupleSymbol a)) =
      ∑ j, milnorKNorm K (D j) n
        (milnorKTupleSymbol (Units.map ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)).toMonoidHom ∘ a)) := by
  intro pb hFinite
  simpa only [milnorKTransport_tupleSymbol] using
    milnorKNorm_map_eq_sum_tensorProductPiEquiv ε n (milnorKTupleSymbol a)

/-- The existing native linear field-map interface gives the identical homogeneous formula. -/
example (ε : (K ⊗[F] E) ≃ₐ[K] (∀ j, D j)) (n : ℕ) (x : MilnorKTheory E n) :
    let pb := Field.powerBasisOfFiniteOfSeparable F E
    let _ : ∀ j, FiniteDimensional K (D j) :=
      fun j => (Classical.choose (pb.exists_powerBasis_of_tensorProductPiEquiv ε j)).finite
    milnorKTheoryMap (algebraMap F K) n (milnorKNorm F E n x) =
      ∑ j, milnorKNorm K (D j) n
        (milnorKTheoryMap ((Pi.evalRingHom D j).comp
          (ε.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) n x) := by
  intro pb hFinite
  simpa only [milnorKTheoryMap_eq_transport, AddMonoidHom.coe_toIntLinearMap] using
    milnorKNorm_map_eq_sum_tensorProductPiEquiv ε n x

end
