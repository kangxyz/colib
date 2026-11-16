/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicTopology.ConstantCoordinateAWComponent
public import Colib.AlgebraicTopology.ConstantCoordinateUnitInsertion
/-! # Constant augmentation identifies the native simplicial and chain units -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial
namespace AlgebraicTopology
variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [HasFiniteCoproducts C]

/-- The original simplicial right unit followed by AW and augmentation is exactly
the native chain right unit, not merely some isomorphism of its endpoints. -/
theorem constantCoordinateAWSourceIso_unit (M : SimplicialObject C) :
    (alternatingFaceMapComplex C).map (ρ_ M).inv ≫
      (constantCoordinateAWSourceIso M (𝟙_ C)).hom =
    (HomologicalComplex.rightUnitor ((alternatingFaceMapComplex C).obj M)).inv := by
  ext n : 1
  change (ρ_ (M.obj (op ⦋n⦌))).inv ≫
      (constantCoordinateAWSourceIso M (𝟙_ C)).hom.f n =
    (HomologicalComplex.rightUnitor' ((alternatingFaceMapComplex C).obj M)).inv n
  rw [constantCoordinateAWSourceIso_hom_f, HomologicalComplex.rightUnitor'_inv]
  simp only [ChainComplex.single₀ObjXSelf, Iso.refl_inv]
  erw [whiskerLeft_id, Category.id_comp]
  rfl

/-- The actual simplicial coordinate insertion, followed by AW, is homotopic to
tensoring with the actual degree-zero coordinate after the native chain unit. -/
def constantCoordinateUnitInsertionHomotopy (M N : SimplicialObject C)
    (b : (SimplicialObject.const C).obj (𝟙_ C) ⟶ N) :
    Homotopy
      ((alternatingFaceMapComplex C).map ((ρ_ M).inv ≫ (M ◁ b)) ≫
        alexanderWhitney M N)
      (constantCoordinateUnitInsertion ((alternatingFaceMapComplex C).obj M) N b) := by
  have h := (constantCoordinateAWSourceHomotopy M N (𝟙_ C) b).compLeft
    ((alternatingFaceMapComplex C).map (ρ_ M).inv)
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc,
    ← constantCoordinateAWSourceIso_unit, constantCoordinateUnitInsertion] using h

end AlgebraicTopology
