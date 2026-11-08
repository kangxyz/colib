/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImage

/-!
# The full right exterior and its actual remaining image incidence

Keep the first support and the full last-pair incidence in their original order.
The latter maps to its existing native scheme-theoretic image. Base change gives
the finite map of full exteriors and its remaining-diagonal Cartesian square.
The native triple associator identifies the common triple's actual outer map.

Finiteness uses the last two correspondences in their given direction. Neither
flatness of the first support over the middle scheme nor admissibility of any
transposed correspondence is assumed. Nilpotents and all components are retained.
The cycle identities transport arbitrary native cycles; they do not identify
the right Tor bracket or prove associativity.

Source comparison: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Incidence/RightComposition.lean, blob
856b38b20a15444e6491366eb2406f21124bfdc5, outer-map geometry only.
Composition/Cycles/RightFirstStageWeightedRemainingCoefficient.lean, blob
5771cc85d24a32f3610872f2a94d457154d1673b, records the separate weighted
remaining-cycle obligation; that comparison is not asserted here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The original first support times the full last-pair incidence over the base. -/
abbrev correspondenceRightIntermediateSupportProduct : Scheme.{u} :=
  pullback (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)
    (correspondenceIncidenceLeft g h i w v ≫ g)

/-- The literal projection to the original last-pair incidence. -/
abbrev correspondenceRightExteriorProjection :
    correspondenceRightIntermediateSupportProduct f g h i z w v ⟶
      correspondenceIncidence g h i w v :=
  pullback.snd _ _

/-- Impose the remaining Y diagonal, without changing the right triple scheme. -/
abbrev correspondenceRightTripleIncidenceToSupportProduct :
    correspondenceRightTripleIncidence f g h i z w v ⟶
      correspondenceRightIntermediateSupportProduct f g h i z w v :=
  pullback.mapDesc ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
    (correspondenceIncidenceLeft g h i w v) g

instance isClosedImmersion_correspondenceRightTripleIncidenceToSupportProduct
    [IsSeparated g] :
    IsClosedImmersion (correspondenceRightTripleIncidenceToSupportProduct f g h i z w v) := by
  dsimp only [correspondenceRightTripleIncidenceToSupportProduct]
  infer_instance

/-- The entire last-pair scheme-theoretic image, exterior to the first support. -/
abbrev correspondenceRightIntermediateImageProduct : Scheme.{u} :=
  pullback (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)
    (((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g)

/-- The remaining incidence uses the source of the last-pair image, not its target. -/
abbrev correspondenceRightImageIncidence : Scheme.{u} :=
  pullback ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
    ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i)

/-- The actual full exterior map, with the first support unchanged. -/
def correspondenceRightIntermediateImageMap :
    correspondenceRightIntermediateSupportProduct f g h i z w v ⟶
      correspondenceRightIntermediateImageProduct f g h i z w v :=
  pullback.map _ _ _ _ (𝟙 (integralComponentAt z).subscheme)
    (correspondenceIncidenceMap g h i w v).toImage (𝟙 S)
    (by simp) (by simp)

/-- Factor the right-parenthesized triple through the actual last-pair image. -/
def correspondenceRightTripleToImageIncidence :
    correspondenceRightTripleIncidence f g h i z w v ⟶
      correspondenceRightImageIncidence f g h i z w v :=
  pullback.map _ _ _ _ (𝟙 (integralComponentAt z).subscheme)
    (correspondenceIncidenceMap g h i w v).toImage (𝟙 Y)
    (by simp) (by simp)

/-- The common triple uses the native associator before the same actual image map. -/
def correspondenceTripleToRightImageIncidence :
    correspondenceTripleIncidence f g h i z w v ⟶
      correspondenceRightImageIncidence f g h i z w v :=
  (correspondenceTripleIncidenceAssoc f g h i z w v).hom ≫
    correspondenceRightTripleToImageIncidence f g h i z w v

/-- The remaining Y diagonal on the entire image exterior. -/
abbrev correspondenceRightImageIncidenceInclusion :
    correspondenceRightImageIncidence f g h i z w v ⟶
      correspondenceRightIntermediateImageProduct f g h i z w v :=
  pullback.mapDesc ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
    ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) g

instance isClosedImmersion_correspondenceRightImageIncidenceInclusion [IsSeparated g] :
    IsClosedImmersion (correspondenceRightImageIncidenceInclusion f g h i z w v) := by
  dsimp only [correspondenceRightImageIncidenceInclusion]
  infer_instance

/-- The two actual routes to the full image exterior agree. -/
@[reassoc]
theorem correspondenceRightTripleToImageIncidence_inclusion :
    correspondenceRightTripleToImageIncidence f g h i z w v ≫
        correspondenceRightImageIncidenceInclusion f g h i z w v =
      correspondenceRightTripleIncidenceToSupportProduct f g h i z w v ≫
        correspondenceRightIntermediateImageMap f g h i z w v := by
  apply pullback.hom_ext <;>
    simp [correspondenceRightTripleToImageIncidence, correspondenceRightImageIncidenceInclusion,
      correspondenceRightTripleIncidenceToSupportProduct, correspondenceRightIntermediateImageMap,
      pullback.mapDesc, pullback.map, Category.assoc]

/-- The right remaining square is a genuine scheme-theoretic pullback. -/
theorem correspondenceRightTripleToImageIncidence_isPullback :
    IsPullback (correspondenceRightTripleToImageIncidence f g h i z w v)
      (correspondenceRightTripleIncidenceToSupportProduct f g h i z w v)
      (correspondenceRightImageIncidenceInclusion f g h i z w v)
      (correspondenceRightIntermediateImageMap f g h i z w v) := by
  let A := (integralComponentAt z).subschemeι ≫ pullback.snd f g
  let B := correspondenceIncidenceLeft g h i w v
  let C := (correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i
  let m₀ := pullback.map (A ≫ g) (B ≫ g) g g A B (𝟙 S) (by simp) (by simp)
  let m₁ := pullback.map (A ≫ g) (C ≫ g) g g A C (𝟙 S) (by simp) (by simp)
  have hm : correspondenceRightIntermediateImageMap f g h i z w v ≫ m₁ = m₀ := by
    apply pullback.hom_ext <;>
      simp [m₀, m₁, A, B, C, correspondenceRightIntermediateImageMap, Category.assoc]
  have ht : correspondenceRightTripleToImageIncidence f g h i z w v ≫
      (pullback.fst A C ≫ A) = pullback.fst A B ≫ A := by
    simp [A, B, C, correspondenceRightTripleToImageIncidence]
  refine IsPullback.of_right (h₁₂ := pullback.fst A C ≫ A) (h₂₂ := m₁)
    (v₁₃ := pullback.diagonal g) ?_
    (correspondenceRightTripleToImageIncidence_inclusion f g h i z w v)
    (pullback_map_diagonal_isPullback A C g)
  rw [ht, hm]
  exact pullback_map_diagonal_isPullback A B g

/-- The actual remaining ideal pulls back as an ideal sheaf, retaining nilpotents. -/
theorem ker_correspondenceRightTripleIncidenceToSupportProduct [IsSeparated g] :
    (correspondenceRightTripleIncidenceToSupportProduct f g h i z w v).ker =
      (correspondenceRightImageIncidenceInclusion f g h i z w v).ker.comap
        (correspondenceRightIntermediateImageMap f g h i z w v) := by
  let sq := (correspondenceRightTripleToImageIncidence_isPullback f g h i z w v).flip
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- Finiteness of the whole exterior map uses only the actual last-pair finite image map. -/
theorem isFinite_correspondenceRightIntermediateImageMap [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v) :
    IsFinite (correspondenceRightIntermediateImageMap f g h i z w v) := by
  let := isFinite_correspondenceIncidenceToImage g h i w v hw hv
  unfold correspondenceRightIntermediateImageMap
  exact MorphismProperty.pullbackMap (P := @IsFinite)
    inferInstance inferInstance (by simp) (by simp)

/-- The right triple-to-image map is finite without flatness of the first support. -/
theorem isFinite_correspondenceRightTripleToImageIncidence [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v) :
    IsFinite (correspondenceRightTripleToImageIncidence f g h i z w v) := by
  let := isFinite_correspondenceIncidenceToImage g h i w v hw hv
  unfold correspondenceRightTripleToImageIncidence
  exact MorphismProperty.pullbackMap (P := @IsFinite)
    inferInstance inferInstance (by simp) (by simp)

/-- The common triple has the same finite map after the native associator. -/
theorem isFinite_correspondenceTripleToRightImageIncidence [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v) :
    IsFinite (correspondenceTripleToRightImageIncidence f g h i z w v) := by
  let := isFinite_correspondenceRightTripleToImageIncidence f g h i z w v hw hv
  dsimp only [correspondenceTripleToRightImageIncidence]
  infer_instance

/-- The original first support supplies the source coordinate of the right image incidence. -/
abbrev correspondenceRightImageIncidenceSource :
    correspondenceRightImageIncidence f g h i z w v ⟶ X :=
  pullback.fst _ _ ≫ (integralComponentAt z).subschemeι ≫ pullback.fst f g

/-- The full last-pair image supplies the final target coordinate. -/
abbrev correspondenceRightImageIncidenceTarget :
    correspondenceRightImageIncidence f g h i z w v ⟶ W :=
  pullback.snd _ _ ≫ (correspondenceIncidenceMap g h i w v).imageι ≫ pullback.snd g i

/-- The outer coordinates agree over the original base. -/
@[reassoc]
theorem correspondenceRightImageIncidence_condition :
    correspondenceRightImageIncidenceSource f g h i z w v ≫ f =
      correspondenceRightImageIncidenceTarget f g h i z w v ≫ i := by
  calc
    _ = pullback.fst _ _ ≫
        (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g) := by
      simp only [correspondenceRightImageIncidenceSource, Category.assoc, pullback.condition]
    _ = pullback.snd _ _ ≫
        (((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g) := by
      simpa only [Category.assoc] using congrArg (fun e => e ≫ g)
        (pullback.condition (f := (integralComponentAt z).subschemeι ≫ pullback.snd f g)
          (g := (correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i))
    _ = _ := by
      simp only [correspondenceRightImageIncidenceTarget, Category.assoc, pullback.condition]

/-- The actual final map of the full right image incidence. -/
def correspondenceRightImageIncidenceMap :
    correspondenceRightImageIncidence f g h i z w v ⟶ pullback f i :=
  pullback.lift (correspondenceRightImageIncidenceSource f g h i z w v)
    (correspondenceRightImageIncidenceTarget f g h i z w v)
    (correspondenceRightImageIncidence_condition f g h i z w v)

@[reassoc (attr := simp)]
theorem correspondenceRightImageIncidenceMap_fst :
    correspondenceRightImageIncidenceMap f g h i z w v ≫ pullback.fst f i =
      correspondenceRightImageIncidenceSource f g h i z w v := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem correspondenceRightImageIncidenceMap_snd :
    correspondenceRightImageIncidenceMap f g h i z w v ≫ pullback.snd f i =
      correspondenceRightImageIncidenceTarget f g h i z w v := pullback.lift_snd _ _ _

/-- Factoring the right triple through the full image leaves the actual output map unchanged. -/
@[reassoc (attr := simp)]
theorem correspondenceRightTripleToImageIncidence_map :
    correspondenceRightTripleToImageIncidence f g h i z w v ≫
        correspondenceRightImageIncidenceMap f g h i z w v =
      correspondenceRightTripleIncidenceMap f g h i z w v := by
  apply pullback.hom_ext <;>
    simp [Category.assoc, correspondenceRightTripleToImageIncidence,
      correspondenceRightImageIncidenceSource, correspondenceRightImageIncidenceTarget]

/-- The original common triple retains its literal source-target map. -/
@[reassoc (attr := simp)]
theorem correspondenceTripleToRightImageIncidence_map :
    correspondenceTripleToRightImageIncidence f g h i z w v ≫
        correspondenceRightImageIncidenceMap f g h i z w v =
      correspondenceTripleIncidenceMap f g h i z w v := by
  simp only [correspondenceTripleToRightImageIncidence, Category.assoc,
    correspondenceRightTripleToImageIncidence_map, correspondenceTripleIncidenceAssoc_map]

/-- The right image incidence remains finite over the original source, in the original direction. -/
theorem isFinite_correspondenceRightImageIncidenceSource [IsSeparated i] [LocallyOfFiniteType i]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v) :
    IsFinite (correspondenceRightImageIncidenceSource f g h i z w v) := by
  let := isFinite_correspondenceIntermediateImageSource g h i w v hw hv
  let := hz.1
  dsimp only [correspondenceRightImageIncidenceSource]
  infer_instance

/-- Finiteness of the final map follows by separated-target cancellation. -/
theorem isFinite_correspondenceRightImageIncidenceMap [IsSeparated i] [LocallyOfFiniteType i]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v) :
    IsFinite (correspondenceRightImageIncidenceMap f g h i z w v) := by
  let := isFinite_correspondenceRightImageIncidenceSource f g h i z w v hz hw hv
  have : IsFinite (correspondenceRightImageIncidenceMap f g h i z w v ≫ pullback.fst f i) := by
    simpa only [correspondenceRightImageIncidenceMap_fst] using
      (inferInstance : IsFinite (correspondenceRightImageIncidenceSource f g h i z w v))
  exact IsFinite.of_comp (correspondenceRightImageIncidenceMap f g h i z w v) (pullback.fst f i)

/-- Native signed pushforward respects the genuine remaining-diagonal square. -/
theorem finiteCyclePushforward_rightImageIncidence [IsSeparated g] [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (c : AlgebraicCycle (correspondenceRightTripleIncidence f g h i z w v) ℤ) :
    letI := isFinite_correspondenceRightTripleToImageIncidence f g h i z w v hw hv
    letI := isFinite_correspondenceRightIntermediateImageMap f g h i z w v hw hv
    finiteCyclePushforward (correspondenceRightImageIncidenceInclusion f g h i z w v)
        (finiteCyclePushforward (correspondenceRightTripleToImageIncidence f g h i z w v) c) =
      finiteCyclePushforward (correspondenceRightIntermediateImageMap f g h i z w v)
        (finiteCyclePushforward
          (correspondenceRightTripleIncidenceToSupportProduct f g h i z w v) c) := by
  let := isFinite_correspondenceRightTripleToImageIncidence f g h i z w v hw hv
  let := isFinite_correspondenceRightIntermediateImageMap f g h i z w v hw hv
  simp only [finiteCyclePushforward_comp_apply,
    correspondenceRightTripleToImageIncidence_inclusion]

/-- Pushing any given common triple cycle through the right image preserves its actual output. -/
theorem finiteCyclePushforward_tripleToRightImageIncidence
    [IsSeparated i] [LocallyOfFiniteType i]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (c : AlgebraicCycle (correspondenceTripleIncidence f g h i z w v) ℤ) :
    letI := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
    letI := isFinite_correspondenceRightImageIncidenceMap f g h i z w v hz hw hv
    letI := isFinite_correspondenceTripleIncidenceMap f g h i z w v hz hw hv
    finiteCyclePushforward (correspondenceRightImageIncidenceMap f g h i z w v)
        (finiteCyclePushforward (correspondenceTripleToRightImageIncidence f g h i z w v) c) =
      finiteCyclePushforward (correspondenceTripleIncidenceMap f g h i z w v) c := by
  let := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
  let := isFinite_correspondenceRightImageIncidenceMap f g h i z w v hz hw hv
  let := isFinite_correspondenceTripleIncidenceMap f g h i z w v hz hw hv
  simp only [finiteCyclePushforward_comp_apply, correspondenceTripleToRightImageIncidence_map]

end Stacks.Chow
