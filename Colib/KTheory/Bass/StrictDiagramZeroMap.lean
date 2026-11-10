/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.StrictDiagram
public import Colib.Topology.Prespectrum.StrictSquareZeroMap

/-!
# The actual Bass diagram functor preserves literal zero maps

The pointwise zero transformation is natural because the original coefficient maps preserve
basepoints. The existing Bass diagram functor sends this same transformation to the pointwise
zero transformation, by the actual reduced cylinder relations at each corner. This supplies the
endpoint equality needed to cast a whole Bass image of an original null track. It does not
construct that whole image or the two-parameter comparison with the original Bass seed.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass
variable {C : Type u} [Category.{v} C]

/-- The literal pointwise zero transformation on the unchanged coefficient diagrams. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramZeroMap.lean:28-37"
  "adaptation" "Original coefficient maps, null tracks and independent parameters retained"]
def diagramZeroMap (F G : C ⥤ LoopPrespectrum.{w}) : F ⟶ G where
  app X := zeroHom (F.obj X) (G.obj X)
  naturality {X Y} f := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    exact ((G.map f).map_point n).symm

/-- Each original Bass component sends the same zero transformation to the actual zero map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramZeroMap.lean:38-45"
  "adaptation" "Original coefficient maps, null tracks and independent parameters retained"]
theorem strictDiagramFunctor_map_zero_app (Q : C ⥤ Arrow (Arrow C))
    (F G : C ⥤ LoopPrespectrum.{w}) (X : C) :
    ((strictDiagramFunctor Q).map (diagramZeroMap F G)).app X =
      zeroHom (((strictDiagramFunctor Q).obj F).obj X)
        (((strictDiagramFunctor Q).obj G).obj X) :=
  strictSquareLoopedConeFunctor_map_eq_zero _ rfl rfl rfl rfl

/-- The original Bass functor preserves pointwise zero as an equality of transformations. -/
@[colib_tag "COL-0516", colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramZeroMap.lean:46-54"
  "adaptation" "Original coefficient maps, null tracks and independent parameters retained"]
theorem strictDiagramFunctor_map_zero (Q : C ⥤ Arrow (Arrow C))
    (F G : C ⥤ LoopPrespectrum.{w}) :
    (strictDiagramFunctor Q).map (diagramZeroMap F G) =
      diagramZeroMap ((strictDiagramFunctor Q).obj F) ((strictDiagramFunctor Q).obj G) := by
  apply NatTrans.ext
  funext X
  exact strictDiagramFunctor_map_zero_app Q F G X

end KTheory.Bass
