/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicTopology.ConstantCoordinateAWUnit
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
/-! # The constant-coordinate AW square after actual additive change and localization -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicTopology
variable {C D : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [HasFiniteCoproducts C]
  [Category D] [Abelian D] [HasDerivedCategory D]

/-- Under actual additive coefficient change and localization, original simplicial
unit-coordinate insertion followed by AW is the native chain tensor-coordinate insertion. -/
theorem constantCoordinateUnitInsertion_localization (F : C ⥤ D) [F.Additive]
    (M N : SimplicialObject C) (b : (SimplicialObject.const C).obj (𝟙_ C) ⟶ N) :
    let L := F.mapHomologicalComplex (.down ℕ) ⋙
      ComplexShape.embeddingDownNat.extendFunctor D ⋙ DerivedCategory.Q
    L.map ((alternatingFaceMapComplex C).map ((ρ_ M).inv ≫ (M ◁ b)) ≫
      alexanderWhitney M N) =
    L.map (constantCoordinateUnitInsertion ((alternatingFaceMapComplex C).obj M) N b) := by
  intro L
  exact DerivedCategory.Q_map_eq_of_homotopy _
    ((F.mapHomotopy (constantCoordinateUnitInsertionHomotopy M N b)).extend
      ComplexShape.embeddingDownNat)

end AlgebraicTopology
