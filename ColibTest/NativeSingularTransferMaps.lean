/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Singular.Maps

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.PresheafWithTransfers
open AlgebraicGeometry.Scheme
open scoped Simplicial

universe v u

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)
  {X Y : Cor k} (α : X ⟶ Y)

example (n : ℕ) : (singularObj P X).X n = sections P (Cor.simplexProduct X n) := rfl

example (n : ℕ) :
    (singularTransfer P α).f n = transfer P (Cor.simplexExterior n α) := rfl

example (i j : ℕ) :
    transfer P (Cor.simplexExterior i α) ≫ (singularObj P X).d i j =
      (singularObj P Y).d i j ≫ transfer P (Cor.simplexExterior j α) :=
  singularTransfer_comm P α i j

example : singularTransfer P (-α) = -singularTransfer P α := singularTransfer_neg P α

example : singularTransfer P (0 : X ⟶ Y) = 0 := singularTransfer_zero P X Y

example (m : ℤ) : singularTransfer P (m • α) = m • singularTransfer P α :=
  singularTransfer_zsmul P m α

example : (singularObj P X).d 1 0 =
    transfer P ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite)
      ((AlgebraicSimplex.cosimplicialSmoothSite k).δ (0 : Fin 2)))) -
    transfer P ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite)
      ((AlgebraicSimplex.cosimplicialSmoothSite k).δ (1 : Fin 2)))) := by
  rw [singularObj_d]
  have h {A : Type v} [AddCommGroup A] (f : Fin 2 → A) :
      (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • f i) = f 0 - f 1 := by
    simp [Fin.sum_univ_two, sub_eq_add_neg]
  exact h (fun i : Fin 2 =>
    transfer P ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite)
      ((AlgebraicSimplex.cosimplicialSmoothSite k).δ i))))
