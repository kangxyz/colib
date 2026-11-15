/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import StacksFrontier.AlgebraicTopology.AlexanderWhitneyConstant

/-! # AW and a constant coordinate, retaining the unnormalized chains

The constant chain is reduced using its native augmentation homotopy equivalence,
not by asserting its positive-degree objects vanish.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicTopology
variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [HasFiniteCoproducts C]

/-- The original constant-coordinate AW composite is homotopic to the composite
through the genuine constant-chain augmentation and its inverse. -/
def constantCoordinateAWHomotopy (M N : SimplicialObject C) (A : C)
    (b : (SimplicialObject.const C).obj A ⟶ N) :
    Homotopy
      ((alternatingFaceMapComplex C).map (M ◁ b) ≫ alexanderWhitney M N)
      ((alexanderWhitney M ((SimplicialObject.const C).obj A) ≫
        HomologicalComplex.tensorHom (𝟙 ((alternatingFaceMapComplex C).obj M))
          (constAugmentationEquiv A).hom) ≫
        HomologicalComplex.tensorHom (𝟙 ((alternatingFaceMapComplex C).obj M))
          ((constAugmentationEquiv A).inv ≫ (alternatingFaceMapComplex C).map b)) := by
  let K := (alternatingFaceMapComplex C).obj M
  let e := tensorHomotopyEquivRight K (constAugmentationEquiv A)
  let f := HomologicalComplex.tensorHom (𝟙 K) ((alternatingFaceMapComplex C).map b)
  have h := (e.homotopyHomInvId.compRight f).compLeft
    (alexanderWhitney M ((SimplicialObject.const C).obj A))
  rw [← alexanderWhitney_naturality_right M ((SimplicialObject.const C).obj A) b]
  simpa only [e, f, tensorHomotopyEquivRight, K, Category.assoc, Category.id_comp,
    tensorHom_id_comp] using h.symm

end AlgebraicTopology
