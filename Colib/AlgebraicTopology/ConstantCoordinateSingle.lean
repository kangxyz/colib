/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicTopology.ConstantCoordinateAW
/-! # The actual degree-zero coordinate obtained from the constant augmentation -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace AlgebraicTopology
variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]

/-- The native inverse augmentation has the identity degree-zero component. -/
theorem constAugmentationEquiv_inv_f_zero (A : C) :
    (constAugmentationEquiv A).inv.f 0 = 𝟙 A := by
  exact ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
    (C := (alternatingFaceMapComplex C).obj ((SimplicialObject.const C).obj A)) (𝟙 A)

/-- The coordinate from the single complex is formed with the genuine inverse augmentation. -/
def constantCoordinateSingle (N : SimplicialObject C) (A : C)
    (b : (SimplicialObject.const C).obj A ⟶ N) :
    (ChainComplex.single₀ C).obj A ⟶ (alternatingFaceMapComplex C).obj N :=
  (constAugmentationEquiv A).inv ≫ (alternatingFaceMapComplex C).map b

/-- Its degree-zero component is exactly the given coordinate. -/
theorem constantCoordinateSingle_f_zero (N : SimplicialObject C) (A : C)
    (b : (SimplicialObject.const C).obj A ⟶ N) :
    (constantCoordinateSingle N A b).f 0 = b.app (op ⦋0⦌) := by
  simp [constantCoordinateSingle, constAugmentationEquiv_inv_f_zero]

end AlgebraicTopology
