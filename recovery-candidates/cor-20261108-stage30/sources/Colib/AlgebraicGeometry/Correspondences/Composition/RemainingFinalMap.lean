/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageComponentIncidence

/-!
# Actual final maps of the whole image and each remaining component

The full image incidence embeds in the original remaining triple product, then
maps to the original source and final target. Every actual remaining component
embedding preserves this final map. The map is finite because the whole image
is finite over the original source and the third support is finite in its
original direction. No reversed correspondence or reversed admissibility is used.

Implementation source: motivic revision a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Composition/Cycles/LeftComposition.lean`,
blob bb359ac96107367ce6acce86ebc152f78309ecb3, lines 56-130. These are actual map
and finiteness statements only, not a Tor-cycle comparison.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

local notation3 (prettyPrint := false) "L" => correspondenceLeftImageIncidence f g h i z w v
local notation3 (prettyPrint := false) "r" => correspondenceIncidenceMap f g h z w
local notation3 (prettyPrint := false) "V" => integralComponentAt v
local notation3 (prettyPrint := false) "C" => correspondenceIntermediateImageTarget f g h z w
local notation3 (prettyPrint := false) "B" => (V).subschemeι ≫ pullback.fst h i

/-- The whole image incidence lies in the actual remaining triple product. -/
def correspondenceLeftImageIncidenceToTripleProduct : L ⟶ correspondenceTripleProduct f h i :=
  pullback.map _ _ _ _ (r).imageι (V).subschemeι (𝟙 Z) (by simp) (by simp)

/-- The full image-incidence embedding keeps the actual fourfold ambient inclusion. -/
@[reassoc]
theorem correspondenceLeftImageIncidenceToTripleProduct_ambient :
    correspondenceLeftImageIncidenceToTripleProduct f g h i z w v ≫
        correspondenceTripleInclusion f h i =
      correspondenceLeftImageIncidenceInclusion f g h i z w v ≫
        correspondenceLeftImageProductInclusion f g h i z w v := by
  apply pullback.hom_ext <;>
    simp [correspondenceLeftImageIncidenceToTripleProduct, correspondenceTripleInclusion,
      correspondenceLeftImageIncidenceInclusion, correspondenceLeftImageProductInclusion,
      pullback.mapDesc, pullback.map, Category.assoc]

/-- The original source coordinate of the full remaining image incidence. -/
abbrev correspondenceLeftImageIncidenceSource : L ⟶ X :=
  pullback.fst C B ≫ (r).imageι ≫ pullback.fst f h

/-- The original final target coordinate of the full remaining image incidence. -/
abbrev correspondenceLeftImageIncidenceTarget : L ⟶ W :=
  pullback.snd C B ≫ (V).subschemeι ≫ pullback.snd h i

/-- The genuine whole-image final map is the native outer projection of its actual triple. -/
def correspondenceLeftImageIncidenceMap : L ⟶ pullback f i :=
  correspondenceLeftImageIncidenceToTripleProduct f g h i z w v ≫
    correspondenceTripleOuterProjection f h i

/-- The final map retains the original source projection. -/
@[reassoc (attr := simp)]
theorem correspondenceLeftImageIncidenceMap_fst :
    correspondenceLeftImageIncidenceMap f g h i z w v ≫ pullback.fst f i =
      correspondenceLeftImageIncidenceSource f g h i z w v := by
  simp [correspondenceLeftImageIncidenceMap, correspondenceLeftImageIncidenceToTripleProduct,
    correspondenceLeftImageIncidenceSource, pullback.map, Category.assoc]

/-- The final map retains the original third-support target projection. -/
@[reassoc (attr := simp)]
theorem correspondenceLeftImageIncidenceMap_snd :
    correspondenceLeftImageIncidenceMap f g h i z w v ≫ pullback.snd f i =
      correspondenceLeftImageIncidenceTarget f g h i z w v := by
  simp [correspondenceLeftImageIncidenceMap, correspondenceLeftImageIncidenceToTripleProduct,
    correspondenceLeftImageIncidenceTarget, correspondenceTripleTarget, pullback.map,
    Category.assoc]

/-- The whole image incidence is finite over the original source, in the given direction. -/
theorem isFinite_correspondenceLeftImageIncidenceSource [IsSeparated h] [LocallyOfFiniteType h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v) :
    IsFinite (correspondenceLeftImageIncidenceSource f g h i z w v) := by
  let := hv.1
  let := isFinite_correspondenceIntermediateImageSource f g h z w hz hw
  change IsFinite (pullback.fst C B ≫ ((r).imageι ≫ pullback.fst f h))
  infer_instance

/-- The actual final map is finite by separated-target cancellation. -/
theorem isFinite_correspondenceLeftImageIncidenceMap
    [IsSeparated h] [LocallyOfFiniteType h] [IsSeparated i]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v) :
    IsFinite (correspondenceLeftImageIncidenceMap f g h i z w v) := by
  let := isFinite_correspondenceLeftImageIncidenceSource f g h i z w v hz hw hv
  have : IsFinite (correspondenceLeftImageIncidenceMap f g h i z w v ≫ pullback.fst f i) := by
    simpa only [correspondenceLeftImageIncidenceMap_fst] using
      (inferInstance : IsFinite (correspondenceLeftImageIncidenceSource f g h i z w v))
  exact IsFinite.of_comp _ (pullback.fst f i)

/-- Every actual remaining component retains its original remaining triple inclusion. -/
@[reassoc]
theorem correspondenceRemainingPairToImageIncidence_triple [IsSeparated h]
    (t : correspondenceIncidence f g h z w) :
    correspondenceRemainingPairToImageIncidence f g h i z w v t ≫
        correspondenceLeftImageIncidenceToTripleProduct f g h i z w v =
      correspondenceIncidenceInclusion f h i (r t) v := by
  apply (cancel_mono (correspondenceTripleInclusion f h i)).mp
  rw [Category.assoc, correspondenceLeftImageIncidenceToTripleProduct_ambient,
    ← Category.assoc, correspondenceRemainingPairToImageIncidence_inclusion,
    Category.assoc, correspondenceRemainingSupportToImageExterior_ambient]
  exact (correspondenceIncidence_ambient_comm f h i (r t) v).symm

/-- The final map of each retained remaining component is literally its original incidence map. -/
@[reassoc]
theorem correspondenceRemainingPairToImageIncidence_map [IsSeparated h]
    (t : correspondenceIncidence f g h z w) :
    correspondenceRemainingPairToImageIncidence f g h i z w v t ≫
        correspondenceLeftImageIncidenceMap f g h i z w v =
      correspondenceIncidenceMap f h i (r t) v := by
  rw [correspondenceLeftImageIncidenceMap, ← Category.assoc,
    correspondenceRemainingPairToImageIncidence_triple,
    correspondenceIncidenceInclusion_outerProjection]

/-- Factoring the actual common triple through the whole image preserves its final map. -/
@[reassoc]
theorem correspondenceTripleToLeftImageIncidence_map :
    correspondenceTripleToLeftImageIncidence f g h i z w v ≫
        correspondenceLeftImageIncidenceMap f g h i z w v =
      correspondenceTripleIncidenceMap f g h i z w v := by
  apply pullback.hom_ext <;>
    simp [correspondenceTripleToLeftImageIncidence, correspondenceLeftImageIncidenceSource,
      correspondenceLeftImageIncidenceTarget, correspondenceTripleIncidenceSource,
      correspondenceTripleIncidenceTarget, correspondenceTripleIncidenceFst,
      correspondenceTripleIncidenceSnd, pullback.map, Category.assoc]

end Stacks.Chow
