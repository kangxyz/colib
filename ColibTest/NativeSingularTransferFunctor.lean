/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Singular.Functor

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.PresheafWithTransfers Opposite
open scoped Simplicial

universe v u

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)
  {X Y Z : Cor k} (α : X ⟶ Y) (β : Y ⟶ Z)

example (n : ℕ) :
    Cor.simplexExterior n (α ≫ β) = Cor.simplexExterior n α ≫ Cor.simplexExterior n β :=
  Cor.simplexExterior_comp n α β

example : singularTransfer P (α ≫ β) = singularTransfer P β ≫ singularTransfer P α :=
  singularTransfer_comp P α β

example : singularTransfer P (𝟙 X) = 𝟙 (singularObj P X) := singularTransfer_id P X

example : (singularFunctor P).obj (op X) = singularObj P X := rfl

example : (singularFunctor P).map α.op = singularTransfer P α := rfl

example : (singularFunctor P).map ((α ≫ β).op) =
    (singularFunctor P).map β.op ≫ (singularFunctor P).map α.op :=
  (singularFunctor P).map_comp β.op α.op

example : singularTransfer P ((-α) ≫ β) =
    singularTransfer P β ≫ (-singularTransfer P α) := by
  rw [singularTransfer_comp, singularTransfer_neg]

example : (singularAdditiveFunctor P).obj.map (α + α).op =
    (singularAdditiveFunctor P).obj.map α.op + (singularAdditiveFunctor P).obj.map α.op := by
  change singularTransfer P (α + α) = singularTransfer P α + singularTransfer P α
  exact singularTransfer_add P α α
