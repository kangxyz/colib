/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusSimplicialTensor
public import StacksFrontier.AlgebraicTopology.AlexanderWhitney

/-!
# The reduced-torus presheaf chain span

These are the actual presheaf chain maps from the literal singular correspondence
objects. The AW target is the ordinary total tensor, not the derived tensor.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry.Scheme AlgebraicTopology
open scoped Simplicial TensorProduct
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]

/-- The actual pointwise tensor of integral presheaves is additive in both variables. -/
instance integralPresheafMonoidalPreadditive :
    MonoidalPreadditive ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤
      ModuleCat.{u + 1} ℤ) where
  whiskerLeft_zero := by intros; apply NatTrans.ext; funext U; simp
  zero_whiskerRight := by intros; apply NatTrans.ext; funext U; simp
  whiskerLeft_add := by intros; apply NatTrans.ext; funext U; simp
  add_whiskerRight := by intros; apply NatTrans.ext; funext U; simp

/-- Apply the native chain functor to the actual simplicial presheaf pairing. -/
def reducedTorusPresheafChainPairing (q : ℕ) :
    (alternatingFaceMapComplex _).obj
      (reducedTorusIntSimplicial k q ⊗ reducedTorusIntSimplicial k 1) ⟶
    (alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k (q + 1)) :=
  (alternatingFaceMapComplex _).map (reducedTorusSimplicialTensorProduct k q)

/-- Native AW in the presheaf category, with its true ordinary total-tensor target. -/
def reducedTorusPresheafAW (q : ℕ) :
    (alternatingFaceMapComplex _).obj
      (reducedTorusIntSimplicial k q ⊗ reducedTorusIntSimplicial k 1) ⟶
    HomologicalComplex.tensorObj
      ((alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k q))
      ((alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k 1)) :=
  alexanderWhitney _ _

end AlgebraicGeometry.PresheafWithTransfers
