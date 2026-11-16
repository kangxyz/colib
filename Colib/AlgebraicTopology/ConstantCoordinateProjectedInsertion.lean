/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicTopology.ConstantCoordinateUnitLocalization
/-! # Native first-factor maps and localized coordinate insertion -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicTopology
variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [HasFiniteCoproducts C]

/-- The actual tensor of a first-factor map and a constant coordinate, after the
simplicial unit and AW, agrees up to homotopy with the native chain unit insertion. -/
def constantCoordinateProjectedInsertionHomotopy (P M N : SimplicialObject C)
    (a : P ⟶ M) (b : (SimplicialObject.const C).obj (𝟙_ C) ⟶ N) :
    Homotopy
      ((alternatingFaceMapComplex C).map ((ρ_ P).inv ≫ (a ⊗ₘ b)) ≫
        alexanderWhitney M N)
      ((alternatingFaceMapComplex C).map a ≫
        constantCoordinateUnitInsertion ((alternatingFaceMapComplex C).obj M) N b) := by
  have he : (ρ_ P).inv ≫ (a ⊗ₘ b) = a ≫ ((ρ_ M).inv ≫ (M ◁ b)) := by
    rw [tensorHom_def, ← Category.assoc, ← rightUnitor_inv_naturality, Category.assoc]
  simpa only [he, CategoryTheory.Functor.map_comp, Category.assoc] using
    (constantCoordinateUnitInsertionHomotopy M N b).compLeft
      ((alternatingFaceMapComplex C).map a)

/-- The actual projected coordinate insertion and chain unit-coordinate insertion
coincide after additive coefficient change and actual derived localization. -/
theorem constantCoordinateProjectedInsertion_localization
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (P M N : SimplicialObject C)
    (a : P ⟶ M) (b : (SimplicialObject.const C).obj (𝟙_ C) ⟶ N) :
    let L := F.mapHomologicalComplex (.down ℕ) ⋙
      ComplexShape.embeddingDownNat.extendFunctor D ⋙ DerivedCategory.Q
    L.map ((alternatingFaceMapComplex C).map ((ρ_ P).inv ≫ (a ⊗ₘ b)) ≫
      alexanderWhitney M N) =
    L.map ((alternatingFaceMapComplex C).map a ≫
      constantCoordinateUnitInsertion ((alternatingFaceMapComplex C).obj M) N b) := by
  intro L
  exact DerivedCategory.Q_map_eq_of_homotopy _
    ((F.mapHomotopy (constantCoordinateProjectedInsertionHomotopy P M N a b)).extend
      ComplexShape.embeddingDownNat)

end AlgebraicTopology
