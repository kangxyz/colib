/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.Quillen.RightBaseChangeTensor
import Colib.Algebra.Category.ModuleCat.MatrixImageTensor

/-! Regression properties of the literal tensor functor and original K-map comparison.

Adapted from the Quillen source
`QuillenTest/BalancedTensorBaseChange.lean` at revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

noncomputable section

universe u v w z a

open CategoryTheory MulOpposite
open RightScalarExtension ModuleCat.FiniteProjective

section IndependentUniverses

variable {R : Type u} {S : Type v} {T : Type z} {U : Type a}
variable [Ring R] [Ring S] [Ring T] [Ring U]
variable (f : R →+* S) (g : S →+* T) (h : T →+* U)
variable {M : Type w} [AddCommGroup M] [Module Rᵐᵒᵖ M]

example (m : M) (s : S) (t : T) (q : U) :
    compEquiv (g.comp f) h
        (pure h (compEquiv f g (pure g (pure f m s) t)) q) =
      pure (h.comp (g.comp f)) m (h (g s) * (h t * q)) := by
  simp [mul_assoc]

example :
    (compEquiv (g.comp f) h (M := M)).toLinearMap.comp
        (RightScalarExtension.map h (compEquiv f g).toLinearMap) =
      (compEquiv f (h.comp g) (M := M)).toLinearMap.comp
        (compEquiv g h (M := Tensor f M)).toLinearMap :=
  compEquiv_assoc f g h

example (P : ModuleCat.FiniteProjective.Category.{u, u} Rᵐᵒᵖ) :
    Module.Finite Sᵐᵒᵖ (Tensor f P.obj) ∧ Module.Projective Sᵐᵒᵖ (Tensor f P.obj) :=
  ⟨inferInstance, inferInstance⟩

example (P : ModuleCat.FiniteProjective.Category.{u, u} Rᵐᵒᵖ) (p : P.obj) (s : S) :
    (rightTensorBaseChangeEquiv f P).symm (op s • rightBaseChangeUnit f P p) =
      pure f p s := by
  rw [← rightTensorBaseChangeEquiv_pure, LinearEquiv.symm_apply_apply]

example (P : Matrix.RightModule.ProjectiveMatrices R)
    (y : (Matrix.RightModule.linearMap (P.p.map f)).range) :
    Matrix.RightModule.tensorImageEquiv f P
      (∑ i, pure f (Matrix.RightModule.imageColumn P i) (y.val i)) = y := by
  rw [← Matrix.RightModule.tensorImageEquiv_symm_apply, LinearEquiv.apply_symm_apply]

example {P Q : Matrix.RightModule.ProjectiveMatrices R} (a : P ⟶ Q)
    (x : Tensor f (Matrix.RightModule.linearMap P.p).range) :
    Matrix.RightModule.tensorImageEquiv f Q
        (RightScalarExtension.map f (Matrix.RightModule.imageMap a) x) =
      Matrix.RightModule.imageMap ((Matrix.RightModule.baseChange f).map a)
        (Matrix.RightModule.tensorImageEquiv f P x) :=
  DFunLike.congr_fun (Matrix.RightModule.tensorImageEquiv_naturality f a) x

end IndependentUniverses

section OriginalKMap

variable {R S : Type u} [Ring R] [Ring S]

example (f : R →+* S) (n : ℕ) (x : (exactStructure Rᵐᵒᵖ).K n) :
    (rightTensorBaseChangeExact f).KMap n x = (rightBaseChangeExact f).KMap n x := by
  rw [rightTensorBaseChangeExact_KMap]

end OriginalKMap
