/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.KTheory.GrothendieckComparison.Injectivity

/-!
# The canonical Q-edge loop has its original Grothendieck weight

The closed realized path of each actual Q-morphism represents the unchanged
classical-to-homotopical comparison of the original Q-cocycle. This relates
actual path classes to the previously constructed additive cocycle.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/KTheory/GrothendieckComparison/EdgeCocycle.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and original proofs are retained. -/

@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
open Topology CategoryTheory
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- The original homotopical class of a closed realized Q-edge. -/
def kZeroEdgeClass {X Y : E.QCategory} (f : X ⟶ Y) : E.K 0 :=
  E.kZeroFundamentalGroupEquiv.symm
    (E.qEdgeClass (classifyingFundamentalGroupoidFunctor E.QCategory) f)

/-- Closing an edge by the original zero-apex arrows does not change its cocycle. -/
theorem qGroupoidToGrothendieck_edgeClass {X Y : E.QCategory} (f : X ⟶ Y) :
    E.qGroupoidToGrothendieck (E.qEdgeClass E.toQGroupoid f) =
      Multiplicative.ofAdd (E.qGrothendieckWeight f) := by
  change E.qGroupoidGrothendieckFunctor.map
    (E.toQGroupoid.map (E.fromZero X) ≫ E.toQGroupoid.map f ≫
      inv (E.toQGroupoid.map (E.fromZero Y))) = _
  simp only [Functor.map_comp, Functor.map_inv]
  change (SingleObj.toEnd (Multiplicative E.GrothendieckGroup)).symm
    (E.qEdgeClass (E.toQGroupoid ⋙ E.qGroupoidGrothendieckFunctor) f) = _
  rw [E.toQGroupoid_comp_grothendieckFunctor]
  dsimp only [qEdgeClass]
  simp only [qGrothendieckFunctor, qGrothendieckWeight_fromZero,
    SingleObj.inv_as_inv, SingleObj.comp_as_mul]
  change (1 : Multiplicative E.GrothendieckGroup) * _ * 1 = _
  simp

/-- The original realized closed edge is the comparison of its exact Q-cocycle weight. -/
theorem kZeroEdgeClass_eq_grothendieckToKZero {X Y : E.QCategory} (f : X ⟶ Y) :
    E.kZeroEdgeClass f =
      E.grothendieckToKZero (Multiplicative.ofAdd (E.qGrothendieckWeight f)) := by
  have h : E.qGroupoidToKZero (E.qEdgeClass E.toQGroupoid f) = E.kZeroEdgeClass f := by
    apply E.kZeroFundamentalGroupEquiv.injective
    simp only [qGroupoidToKZero, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, MulEquiv.apply_symm_apply, kZeroEdgeClass]
    apply CategoryTheory.End.ext
    change (classifyingGroupoidCompletionFunctor E.QCategory).map
      (E.toQGroupoid.map (E.fromZero X) ≫ E.toQGroupoid.map f ≫
        inv (E.toQGroupoid.map (E.fromZero Y))) = _
    simp only [Functor.map_comp, Functor.map_inv]
    change (E.qEdgeClass
      (E.toQGroupoid ⋙ classifyingGroupoidCompletionFunctor E.QCategory) f).asHom = _
    exact congrArg CategoryTheory.End.asHom (eq_of_heq (show HEq
      (E.qEdgeClass (E.toQGroupoid ⋙ classifyingGroupoidCompletionFunctor E.QCategory) f)
      (E.qEdgeClass (classifyingFundamentalGroupoidFunctor E.QCategory) f) from by
        rw [toClassifyingGroupoidCompletionFunctor]))
  rw [← h, ← E.qGroupoidToGrothendieck_edgeClass f,
    ← E.grothendieckToKZero_factorization]
  exact congrArg E.qGroupoidToKZero
    (E.grothendieckToQGroupoid_qGroupoidToGrothendieck _).symm

end CategoryTheory.ExactCategory.ExactStructure
