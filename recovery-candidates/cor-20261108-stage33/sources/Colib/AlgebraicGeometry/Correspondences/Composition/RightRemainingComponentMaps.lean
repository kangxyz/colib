/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImage
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageComponentGeometry

/-!
# Original remaining right pairs inside the whole right image incidence

The existing native point-closure comparison factors the original G,H image-point support
through its whole scheme-theoretic image. Base change with the original F support gives
the actual remaining pair's closed immersion into the right image incidence. Both final
coordinates are unchanged. No reversed correspondence or flatness assertion is used.

Only the three-factor point-closure supplier from RemainingImageComponentGeometry is used;
its inputs are the original g,h,i,w,v in that order. The remaining pair is literally
correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t).

References: Stacks 02R4-02R5; independent motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Incidence/RightComposition.lean, the remaining-to-image and final-map argument.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The original last-pair image-point support, factored through its actual whole image. -/
def correspondenceRightRemainingImagePointInclusion
    (t : correspondenceIncidence g h i w v) :
    (integralComponentAt (correspondenceIncidenceMap g h i w v t)).subscheme ⟶
      (correspondenceIncidenceMap g h i w v).image :=
  let e := (exists_correspondenceRemainingImagePointIso g h i w v t).choose
  e.inv ≫ (integralComponentAt ((correspondenceIncidenceMap g h i w v).toImage t)).subschemeι

/-- The actual original adjacent-product support embedding is unchanged. -/
@[reassoc (attr := simp)]
theorem correspondenceRightRemainingImagePointInclusion_imageι
    (t : correspondenceIncidence g h i w v) :
    correspondenceRightRemainingImagePointInclusion g h i w v t ≫
        (correspondenceIncidenceMap g h i w v).imageι =
      (integralComponentAt (correspondenceIncidenceMap g h i w v t)).subschemeι := by
  have he := (exists_correspondenceRemainingImagePointIso g h i w v t).choose_spec
  dsimp only [correspondenceRightRemainingImagePointInclusion]
  rw [Category.assoc, ← he]
  simp

instance isClosedImmersion_correspondenceRightRemainingImagePointInclusion
    (t : correspondenceIncidence g h i w v) :
    IsClosedImmersion (correspondenceRightRemainingImagePointInclusion g h i w v t) := by
  dsimp only [correspondenceRightRemainingImagePointInclusion]
  infer_instance

/-- The actual remaining F,image(G,H) incidence embeds into the whole right image incidence. -/
def correspondenceRightRemainingPairToImageIncidence
    (t : correspondenceIncidence g h i w v) :
    correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t) ⟶
      correspondenceRightImageIncidence f g h i z w v :=
  pullback.map _ _ _ _ (𝟙 (integralComponentAt z).subscheme)
    (correspondenceRightRemainingImagePointInclusion g h i w v t) (𝟙 Y)
    (by simp) (by simp [← Category.assoc])

instance isClosedImmersion_correspondenceRightRemainingPairToImageIncidence
    (t : correspondenceIncidence g h i w v) :
    IsClosedImmersion (correspondenceRightRemainingPairToImageIncidence f g h i z w v t) := by
  unfold correspondenceRightRemainingPairToImageIncidence
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    inferInstance inferInstance (by simp) (by simp [← Category.assoc])

/-- The remaining incidence retains the original source coordinate. -/
@[reassoc (attr := simp)]
theorem correspondenceRightRemainingPairToImageIncidence_source
    (t : correspondenceIncidence g h i w v) :
    correspondenceRightRemainingPairToImageIncidence f g h i z w v t ≫
        correspondenceRightImageIncidenceSource f g h i z w v =
      correspondenceIncidenceLeft f g i z (correspondenceIncidenceMap g h i w v t) := by
  simp [correspondenceRightRemainingPairToImageIncidence,
    correspondenceRightImageIncidenceSource, correspondenceIncidenceLeft, Category.assoc]

/-- The final map is exactly the original remaining pair's source-target map. -/
@[reassoc (attr := simp)]
theorem correspondenceRightRemainingPairToImageIncidence_map
    (t : correspondenceIncidence g h i w v) :
    correspondenceRightRemainingPairToImageIncidence f g h i z w v t ≫
        correspondenceRightImageIncidenceMap f g h i z w v =
      correspondenceIncidenceMap f g i z (correspondenceIncidenceMap g h i w v t) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, correspondenceRightImageIncidenceMap_fst,
      correspondenceRightRemainingPairToImageIncidence_source, correspondenceIncidenceMap_fst]
  · simp [correspondenceRightRemainingPairToImageIncidence,
      correspondenceRightImageIncidenceTarget, correspondenceIncidenceRight, Category.assoc]

end Stacks.Chow
