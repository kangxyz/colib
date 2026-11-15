/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import StacksFrontier.AlgebraicTopology.AlexanderWhitneyConstant
/-! # The native unit insertion uses precisely the (n,0) summand -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
namespace AlgebraicTopology
variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [HasFiniteCoproducts C]

/-- Tensoring with a degree-zero coordinate after the native right unit comparison
has the literal (n,0) component; no positive-degree constant chain is set to zero. -/
theorem rightUnitor_tensorCoordinate_f (K L : ChainComplex C ℕ)
    (b : tensorUnit C (.down ℕ) ⟶ L) (n : ℕ) :
    ((HomologicalComplex.rightUnitor K).inv ≫ HomologicalComplex.tensorHom (𝟙 K) b).f n =
      (ρ_ (K.X n)).inv ≫
        (K.X n ◁ (singleObjXSelf (.down ℕ) 0 (𝟙_ C)).inv) ≫
          (K.X n ◁ b.f 0) ≫ ιTensorObj K L n 0 n (add_zero n) := by
  change (rightUnitor' K).inv n ≫ (HomologicalComplex.tensorHom (𝟙 K) b).f n = _
  rw [rightUnitor'_inv, Category.assoc, Category.assoc, ι_mapBifunctorMap]
  simp only [id_f, curriedTensor_map_app, curriedTensor_obj_map,
    MonoidalCategory.id_whiskerRight]
  erw [Category.id_comp]

end AlgebraicTopology
