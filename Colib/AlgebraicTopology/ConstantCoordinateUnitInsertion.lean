/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicTopology.ConstantCoordinateSingle
public import Colib.AlgebraicTopology.ConstantCoordinateUnitComponent
/-! # The degree-zero coordinate with the native chain tensor unit -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite HomologicalComplex
open scoped Simplicial
namespace AlgebraicTopology
variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [HasFiniteCoproducts C]

/-- Tensor with the original degree-zero coordinate, using the native right unit comparison. -/
def constantCoordinateUnitInsertion (K : ChainComplex C ℕ) (N : SimplicialObject C)
    (b : (SimplicialObject.const C).obj (𝟙_ C) ⟶ N) :
    K ⟶ HomologicalComplex.tensorObj K ((alternatingFaceMapComplex C).obj N) :=
  (HomologicalComplex.rightUnitor K).inv ≫
    HomologicalComplex.tensorHom (𝟙 K) (constantCoordinateSingle N (𝟙_ C) b)

/-- The original coordinate occurs exactly in the native (n,0) summand. -/
theorem constantCoordinateUnitInsertion_f (K : ChainComplex C ℕ) (N : SimplicialObject C)
    (b : (SimplicialObject.const C).obj (𝟙_ C) ⟶ N) (n : ℕ) :
    (constantCoordinateUnitInsertion K N b).f n =
      (ρ_ (K.X n)).inv ≫
        (K.X n ◁ (singleObjXSelf (.down ℕ) 0 (𝟙_ C)).inv) ≫
          (K.X n ◁ b.app (op ⦋0⦌)) ≫
            ιTensorObj K ((alternatingFaceMapComplex C).obj N) n 0 n (add_zero n) := by
  simpa only [constantCoordinateUnitInsertion, constantCoordinateSingle_f_zero] using
    rightUnitor_tensorCoordinate_f K ((alternatingFaceMapComplex C).obj N)
      (constantCoordinateSingle N (𝟙_ C) b) n

end AlgebraicTopology
