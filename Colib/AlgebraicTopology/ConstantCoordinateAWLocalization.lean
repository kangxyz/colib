/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicTopology.ConstantCoordinateAW
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
/-! # The constant-coordinate AW square after actual additive change and localization -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicTopology
variable {C D : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [HasFiniteCoproducts C]
  [Category D] [Abelian D] [HasDerivedCategory D]

/-- The original AW coordinate square equals the augmentation/degree-zero square
under any actual additive coefficient functor followed by extension and localization. -/
theorem constantCoordinateAW_localization (F : C ⥤ D) [F.Additive]
    (M N : SimplicialObject C) (A : C) (b : (SimplicialObject.const C).obj A ⟶ N) :
    let L := F.mapHomologicalComplex (.down ℕ) ⋙
      ComplexShape.embeddingDownNat.extendFunctor D ⋙ DerivedCategory.Q
    L.map ((alternatingFaceMapComplex C).map (M ◁ b) ≫ alexanderWhitney M N) =
    L.map ((alexanderWhitney M ((SimplicialObject.const C).obj A) ≫
      HomologicalComplex.tensorHom (𝟙 ((alternatingFaceMapComplex C).obj M))
        (constAugmentationEquiv A).hom) ≫
      HomologicalComplex.tensorHom (𝟙 ((alternatingFaceMapComplex C).obj M))
        ((constAugmentationEquiv A).inv ≫ (alternatingFaceMapComplex C).map b)) := by
  intro L
  exact DerivedCategory.Q_map_eq_of_homotopy _
    ((F.mapHomotopy (constantCoordinateAWHomotopy M N A b)).extend
      ComplexShape.embeddingDownNat)

end AlgebraicTopology
