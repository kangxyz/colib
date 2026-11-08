/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingProjection
public import Colib.AlgebraicGeometry.Correspondences.Composition.Pushforward

/-!
# The full intermediate image and its remaining incidence

The intermediate image is the native scheme-theoretic image of the whole
original pair incidence. Its exterior product with the third support and its
remaining diagonal pullback are not replaced by reduced or integral schemes.
The original exterior and triple incidence map finitely to these schemes.

The original pair residue degree is unchanged on factoring through its closed
image. All native signed cycle pushforwards retain the entire fibre, including
colliding original labels. The cycle identities here are transport identities
for a given cycle, not the missing Tor/Euler dévissage comparison.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The full scheme-theoretic image of the original pair incidence. -/
abbrev correspondenceIntermediateImage : Scheme.{u} :=
  (correspondenceIncidenceMap f g h z w).image

/-- The target coordinate on the full intermediate image. -/
abbrev correspondenceIntermediateImageTarget : correspondenceIntermediateImage f g h z w ⟶ Z :=
  (correspondenceIncidenceMap f g h z w).imageι ≫ pullback.snd f h

/-- The full intermediate image times the third integral support. -/
abbrev correspondenceLeftIntermediateImageProduct : Scheme.{u} :=
  pullback (correspondenceIntermediateImageTarget f g h z w ≫ h)
    (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)

/-- The full intermediate image after imposing the remaining middle diagonal. -/
abbrev correspondenceLeftImageIncidence : Scheme.{u} :=
  pullback (correspondenceIntermediateImageTarget f g h z w)
    ((integralComponentAt v).subschemeι ≫ pullback.fst h i)

/-- The image exterior is a closed subscheme of the remaining ambient. -/
def correspondenceLeftImageProductInclusion :
    correspondenceLeftIntermediateImageProduct f g h i z w v ⟶
      correspondenceIntersectionAmbient f h i :=
  pullback.map _ _ _ _ (correspondenceIncidenceMap f g h z w).imageι
    (integralComponentAt v).subschemeι (𝟙 S) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
instance isClosedImmersion_correspondenceLeftImageProductInclusion :
    IsClosedImmersion (correspondenceLeftImageProductInclusion f g h i z w v) := by
  unfold correspondenceLeftImageProductInclusion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion (correspondenceIncidenceMap f g h z w).imageι))
    (inferInstanceAs (IsClosedImmersion (integralComponentAt v).subschemeι)) (by simp) (by simp)

/-- The finite image map on the entire first-stage exterior. -/
def correspondenceLeftIntermediateImageMap :
    correspondenceLeftIntermediateSupportProduct f g h i z w v ⟶
      correspondenceLeftIntermediateImageProduct f g h i z w v :=
  pullback.map _ _ _ _ (correspondenceIncidenceMap f g h z w).toImage
    (𝟙 (integralComponentAt v).subscheme) (𝟙 S)
    (by simp [correspondenceIntermediateImageTarget]) (by simp)

/-- The original triple incidence maps to the remaining incidence of the full image. -/
def correspondenceTripleToLeftImageIncidence :
    correspondenceTripleIncidence f g h i z w v ⟶
      correspondenceLeftImageIncidence f g h i z w v :=
  pullback.map _ _ _ _ (correspondenceIncidenceMap f g h z w).toImage
    (𝟙 (integralComponentAt v).subscheme) (𝟙 Z)
    (by simp [correspondenceIntermediateImageTarget]) (by simp)

/-- The remaining diagonal on the full intermediate image exterior. -/
abbrev correspondenceLeftImageIncidenceInclusion :
    correspondenceLeftImageIncidence f g h i z w v ⟶
      correspondenceLeftIntermediateImageProduct f g h i z w v :=
  pullback.mapDesc (correspondenceIntermediateImageTarget f g h z w)
    ((integralComponentAt v).subschemeι ≫ pullback.fst h i) h

instance isClosedImmersion_correspondenceLeftImageIncidenceInclusion [IsSeparated h] :
    IsClosedImmersion (correspondenceLeftImageIncidenceInclusion f g h i z w v) := by
  dsimp only [correspondenceLeftImageIncidenceInclusion]
  infer_instance

/-- Factoring through the full intermediate image does not alter the ambient map. -/
@[reassoc]
theorem correspondenceLeftIntermediateImageMap_inclusion :
    correspondenceLeftIntermediateImageMap f g h i z w v ≫
        correspondenceLeftImageProductInclusion f g h i z w v =
      correspondenceRemainingSupportMap f g h i z w v := by
  apply pullback.hom_ext <;>
    simp [correspondenceLeftIntermediateImageMap, correspondenceLeftImageProductInclusion,
      correspondenceRemainingSupportMap, Category.assoc]

/-- Both diagonal orders retain the exact full-scheme finite map. -/
@[reassoc]
theorem correspondenceTripleToLeftImageIncidence_inclusion :
    correspondenceTripleToLeftImageIncidence f g h i z w v ≫
        correspondenceLeftImageIncidenceInclusion f g h i z w v =
      correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v ≫
        correspondenceLeftIntermediateImageMap f g h i z w v := by
  apply pullback.hom_ext <;>
    simp [correspondenceTripleToLeftImageIncidence, correspondenceLeftImageIncidenceInclusion,
      correspondenceTripleIncidenceToLeftSupportProduct, correspondenceLeftIntermediateImageMap,
      pullback.mapDesc, pullback.map, Category.assoc]

/-- The remaining incidence square over the full finite intermediate image is
Cartesian, not merely a commuting square on point sets. -/
theorem correspondenceTripleToLeftImageIncidence_isPullback :
    IsPullback (correspondenceTripleToLeftImageIncidence f g h i z w v)
      (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v)
      (correspondenceLeftImageIncidenceInclusion f g h i z w v)
      (correspondenceLeftIntermediateImageMap f g h i z w v) := by
  let A := correspondenceIncidenceRight f g h z w
  let B := (integralComponentAt v).subschemeι ≫ pullback.fst h i
  let C := correspondenceIntermediateImageTarget f g h z w
  let m₀ := pullback.map (A ≫ h) (B ≫ h) h h A B (𝟙 S) (by simp) (by simp)
  let m₁ := pullback.map (C ≫ h) (B ≫ h) h h C B (𝟙 S) (by simp) (by simp)
  have hm : correspondenceLeftIntermediateImageMap f g h i z w v ≫ m₁ = m₀ := by
    apply pullback.hom_ext <;>
      simp [m₀, m₁, A, B, C, correspondenceLeftIntermediateImageMap,
        correspondenceIntermediateImageTarget, Category.assoc]
  have ht : correspondenceTripleToLeftImageIncidence f g h i z w v ≫
      (pullback.fst C B ≫ C) = pullback.fst A B ≫ A := by
    simp [A, B, C, correspondenceTripleToLeftImageIncidence,
      correspondenceIntermediateImageTarget, Category.assoc]
  refine IsPullback.of_right (h₁₂ := pullback.fst C B ≫ C) (h₂₂ := m₁)
    (v₁₃ := pullback.diagonal h) ?_
    (correspondenceTripleToLeftImageIncidence_inclusion f g h i z w v)
    (pullback_map_diagonal_isPullback C B h)
  rw [ht, hm]
  exact pullback_map_diagonal_isPullback A B h

/-- The actual remaining ideal is the scheme-theoretic pullback of the image
remaining ideal. Nilpotents and embedded structure are retained. -/
theorem ker_correspondenceTripleToLeftSupportProduct [IsSeparated h] :
    (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v).ker =
      (correspondenceLeftImageIncidenceInclusion f g h i z w v).ker.comap
        (correspondenceLeftIntermediateImageMap f g h i z w v) := by
  let sq := (correspondenceTripleToLeftImageIncidence_isPullback f g h i z w v).flip
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- The finite original incidence map factors finitely through its closed image. -/
theorem isFinite_correspondenceIncidenceToImage [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    IsFinite (correspondenceIncidenceMap f g h z w).toImage := by
  let : IsFinite (correspondenceIncidenceMap f g h z w) :=
    isFinite_correspondenceIncidenceMap f g h z w hz hw
  have : IsFinite ((correspondenceIncidenceMap f g h z w).toImage ≫
      (correspondenceIncidenceMap f g h z w).imageι) := by
    simpa only [Scheme.Hom.toImage_imageι] using
      (inferInstance : IsFinite (correspondenceIncidenceMap f g h z w))
  exact IsFinite.of_comp _ (correspondenceIncidenceMap f g h z w).imageι

/-- Finiteness survives the entire exterior product, without reducing either factor. -/
theorem isFinite_correspondenceLeftIntermediateImageMap [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    IsFinite (correspondenceLeftIntermediateImageMap f g h i z w v) := by
  let := isFinite_correspondenceIncidenceToImage f g h z w hz hw
  unfold correspondenceLeftIntermediateImageMap
  exact MorphismProperty.pullbackMap (P := @IsFinite)
    inferInstance inferInstance (by simp [correspondenceIntermediateImageTarget]) (by simp)

/-- The actual triple-to-image-incidence map is finite, with no flatness claim. -/
theorem isFinite_correspondenceTripleToLeftImageIncidence [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    IsFinite (correspondenceTripleToLeftImageIncidence f g h i z w v) := by
  let := isFinite_correspondenceIncidenceToImage f g h z w hz hw
  unfold correspondenceTripleToLeftImageIncidence
  exact MorphismProperty.pullbackMap (P := @IsFinite)
    inferInstance inferInstance (by simp [correspondenceIntermediateImageTarget]) (by simp)

/-- The whole intermediate image is finite over the original source. The
finite-type hypothesis is exactly that of the imported scheme-image supplier. -/
theorem isFinite_correspondenceIntermediateImageSource [IsSeparated h] [LocallyOfFiniteType h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    IsFinite ((correspondenceIncidenceMap f g h z w).imageι ≫ pullback.fst f h) := by
  let := isFinite_correspondenceIncidenceLeft f g h z w hz hw
  have : IsFinite (correspondenceIncidenceMap f g h z w ≫ pullback.fst f h) := by
    simpa only [correspondenceIncidenceMap_fst] using
      (inferInstance : IsFinite (correspondenceIncidenceLeft f g h z w))
  exact finiteCyclePushforward_isFinite_imageι_comp
    (correspondenceIncidenceMap f g h z w) (pullback.fst f h)

/-- Passing to the full scheme-theoretic image preserves the original residue degree. -/
theorem correspondenceIncidenceToImage_residueDegree
    (t : correspondenceIncidence f g h z w) :
    (correspondenceIncidenceMap f g h z w).toImage.residueDegree t =
      (correspondenceIncidenceMap f g h z w).residueDegree t := by
  have he := residueDegree_comp (correspondenceIncidenceMap f g h z w).toImage
    (correspondenceIncidenceMap f g h z w).imageι t
  simpa only [Scheme.Hom.toImage_imageι, residueDegree_eq_one_of_isClosedImmersion,
    one_mul, mul_one] using he.symm

/-- Finite native cycle pushforward commutes with the actual remaining-diagonal
square. This holds for arbitrary signed cycles on the original triple incidence. -/
theorem finiteCyclePushforward_leftImageIncidence [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (c : AlgebraicCycle (correspondenceTripleIncidence f g h i z w v) ℤ) :
    letI := isFinite_correspondenceTripleToLeftImageIncidence f g h i z w v hz hw
    letI := isFinite_correspondenceLeftIntermediateImageMap f g h i z w v hz hw
    finiteCyclePushforward (correspondenceLeftImageIncidenceInclusion f g h i z w v)
        (finiteCyclePushforward (correspondenceTripleToLeftImageIncidence f g h i z w v) c) =
      finiteCyclePushforward (correspondenceLeftIntermediateImageMap f g h i z w v)
        (finiteCyclePushforward
          (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v) c) := by
  let := isFinite_correspondenceTripleToLeftImageIncidence f g h i z w v hz hw
  let := isFinite_correspondenceLeftIntermediateImageMap f g h i z w v hz hw
  simp only [finiteCyclePushforward_comp_apply, correspondenceTripleToLeftImageIncidence_inclusion]

end Stacks.Chow
