/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicTopology.ConstantCoordinateSingle
/-! # The actual AW-plus-augmentation source isomorphism -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicTopology
variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [HasFiniteCoproducts C]

/-- The native AW map followed by constant augmentation is a genuine chain isomorphism. -/
def constantCoordinateAWSourceIso (M : SimplicialObject C) (A : C) :
    (alternatingFaceMapComplex C).obj (M ⊗ (SimplicialObject.const C).obj A) ≅
      HomologicalComplex.tensorObj ((alternatingFaceMapComplex C).obj M)
        ((ChainComplex.single₀ C).obj A) :=
  asIso (alexanderWhitney M ((SimplicialObject.const C).obj A) ≫
    HomologicalComplex.tensorHom (𝟙 ((alternatingFaceMapComplex C).obj M))
      (constAugmentationEquiv A).hom)

/-- The original coordinate AW morphism factors up to genuine homotopy through the
native chain isomorphism and the actual single-complex coordinate. -/
def constantCoordinateAWSourceHomotopy (M N : SimplicialObject C) (A : C)
    (b : (SimplicialObject.const C).obj A ⟶ N) :
    Homotopy ((alternatingFaceMapComplex C).map (M ◁ b) ≫ alexanderWhitney M N)
      ((constantCoordinateAWSourceIso M A).hom ≫
        HomologicalComplex.tensorHom (𝟙 ((alternatingFaceMapComplex C).obj M))
          (constantCoordinateSingle N A b)) :=
  constantCoordinateAWHomotopy M N A b

end AlgebraicTopology
