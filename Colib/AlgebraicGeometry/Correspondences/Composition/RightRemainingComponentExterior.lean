/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingComponentMaps
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImageComponentEuler
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.GenericPoints

/-!
# The actual remaining F,image(G,H) support inside the full right exterior

Base change the already constructed original G,H image-point inclusion with the
unchanged first support. Its kernel is the full image-component inverse image,
not its radical. The already constructed remaining pair-to-image map is the
remaining Y-diagonal base change of this actual support map. This proves the
closed-support and scalar endpoints needed for the original pair-Tor comparison.
No chosen inverse admissibility, support comparison or flatness is a premise.
References: native closed-immersion kernel base change and Stacks 02R4.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The full actual remaining pair support maps into the full right image exterior. -/
def correspondenceRightRemainingSupportToImageExterior
    (t : correspondenceIncidence g h i w v) :
    correspondenceSupportProduct f g i z (correspondenceIncidenceMap g h i w v t) ⟶
      correspondenceRightIntermediateImageProduct f g h i z w v :=
  pullback.map _ _ _ _ (𝟙 (integralComponentAt z).subscheme)
    (correspondenceRightRemainingImagePointInclusion g h i w v t) (𝟙 S)
    (by simp) (by simp [← Category.assoc])

instance isClosedImmersion_correspondenceRightRemainingSupportToImageExterior
    (t : correspondenceIncidence g h i w v) :
    IsClosedImmersion (correspondenceRightRemainingSupportToImageExterior f g h i z w v t) := by
  unfold correspondenceRightRemainingSupportToImageExterior
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    inferInstance inferInstance (by simp) (by simp [← Category.assoc])

/-- Both second-factor projections are the original image-point inclusion. -/
@[reassoc]
theorem correspondenceRightRemainingSupportToImageExterior_projection
    (t : correspondenceIncidence g h i w v) :
    correspondenceRightRemainingSupportToImageExterior f g h i z w v t ≫
        correspondenceRightImageExteriorProjection f g h i z w v =
      pullback.snd _ _ ≫ correspondenceRightRemainingImagePointInclusion g h i w v t := by
  simp [correspondenceRightRemainingSupportToImageExterior,
    correspondenceRightImageExteriorProjection]

/-- The support inclusion is literally base change of the actual original image-point inclusion. -/
theorem correspondenceRightRemainingSupportToImageExterior_isPullback
    (t : correspondenceIncidence g h i w v) :
    IsPullback (correspondenceRightRemainingSupportToImageExterior f g h i z w v t)
      (pullback.snd _ _)
      (correspondenceRightImageExteriorProjection f g h i z w v)
      (correspondenceRightRemainingImagePointInclusion g h i w v t) := by
  let b := correspondenceRightRemainingImagePointInclusion g h i w v t
  let u := correspondenceRightRemainingSupportToImageExterior f g h i z w v t
  let a := ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g
  let c := ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g
  have hb : b ≫ c =
      (integralComponentAt (correspondenceIncidenceMap g h i w v t)).subschemeι ≫
        pullback.fst g i ≫ g := by
    simp only [b, c, ← Category.assoc,
      correspondenceRightRemainingImagePointInclusion_imageι]
  have hp : IsPullback (pullback.snd _ _) (u ≫ pullback.fst _ _) (b ≫ c) a := by
    rw [hb]
    simpa only [u, correspondenceRightRemainingSupportToImageExterior, pullback.map,
      pullback.lift_fst, Category.comp_id, a, Category.assoc] using
      (IsPullback.of_hasPullback
        ((integralComponentAt z).subschemeι ≫ pullback.snd f g ≫ g)
        ((integralComponentAt (correspondenceIncidenceMap g h i w v t)).subschemeι ≫
          pullback.fst g i ≫ g)).flip
  exact (hp.of_bot
    (correspondenceRightRemainingSupportToImageExterior_projection f g h i z w v t).symm
    (IsPullback.of_hasPullback a c).flip).flip

/-- The actual support map kernel is the full inverse-image ideal, with all nilpotents. -/
theorem correspondenceRightRemainingSupportToImageExterior_ker
    (t : correspondenceIncidence g h i w v) :
    (correspondenceRightRemainingSupportToImageExterior f g h i z w v t).ker =
      correspondenceRightRemainingImageComponent f g h i z w v t := by
  let H := correspondenceRightRemainingSupportToImageExterior_isPullback f g h i z w v t
  rw [← H.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  simp only [correspondenceRightRemainingImagePointInclusion,
    correspondenceRightRemainingImageComponent, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_subschemeι]

/-- The remaining original Y self-product map is unchanged on the actual component support. -/
@[reassoc]
theorem correspondenceRightRemainingSupportToImageExterior_middle
    (t : correspondenceIncidence g h i w v) :
    correspondenceRightRemainingSupportToImageExterior f g h i z w v t ≫
        correspondenceRightImageMiddlePair f g h i z w v =
      correspondenceSupportProductInclusion f g i z (correspondenceIncidenceMap g h i w v t) ≫
        correspondenceMiddlePair f g i := by
  apply pullback.hom_ext <;>
    simp [correspondenceRightRemainingSupportToImageExterior,
      correspondenceRightImageMiddlePair, correspondenceSupportProductInclusion,
      correspondenceMiddlePair, Category.assoc]

/-- The already constructed actual pair-to-image map preserves the full support point. -/
@[reassoc]
theorem correspondenceRightRemainingPairToImageIncidence_inclusion
    (t : correspondenceIncidence g h i w v) :
    correspondenceRightRemainingPairToImageIncidence f g h i z w v t ≫
        correspondenceRightImageIncidenceInclusion f g h i z w v =
      correspondenceIncidenceToSupportProduct f g i z (correspondenceIncidenceMap g h i w v t) ≫
        correspondenceRightRemainingSupportToImageExterior f g h i z w v t := by
  apply pullback.hom_ext <;>
    simp [correspondenceRightRemainingPairToImageIncidence,
      correspondenceRightImageIncidenceInclusion,
      correspondenceRightRemainingSupportToImageExterior, pullback.mapDesc, pullback.map,
      Category.assoc]

/-- The remaining diagonal point is the literal original pair middle point. -/
@[reassoc]
theorem correspondenceRightRemainingPairToImageIncidence_middle
    (t : correspondenceIncidence g h i w v) :
    correspondenceRightRemainingPairToImageIncidence f g h i z w v t ≫
        (pullback.fst ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
          ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫
            ((integralComponentAt z).subschemeι ≫ pullback.snd f g)) =
      correspondenceIncidenceInclusion f g i z (correspondenceIncidenceMap g h i w v t) ≫
        correspondenceTripleMiddle f g i := by
  simp [correspondenceRightRemainingPairToImageIncidence, correspondenceIncidenceInclusion,
    correspondenceTripleMiddle, Category.assoc]

/-- The actual remaining incidence is the genuine Y-diagonal base change of the full support. -/
theorem correspondenceRightRemainingPairToImageIncidence_isPullback
    (t : correspondenceIncidence g h i w v) :
    IsPullback (correspondenceRightRemainingPairToImageIncidence f g h i z w v t)
      (correspondenceIncidenceToSupportProduct f g i z (correspondenceIncidenceMap g h i w v t))
      (correspondenceRightImageIncidenceInclusion f g h i z w v)
      (correspondenceRightRemainingSupportToImageExterior f g h i z w v t) := by
  let q := correspondenceIncidenceMap g h i w v t
  let u := correspondenceRightRemainingSupportToImageExterior f g h i z w v t
  let a := correspondenceIncidenceToSupportProduct f g i z q
  let b := correspondenceIncidenceInclusion f g i z q
  let mT := correspondenceRightImageMiddlePair f g h i z w v
  let kL := pullback.fst ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
    ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫
      ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
  have H := (isPullback_correspondenceAmbientIncidence f g i z q).flip.paste_vert
    (correspondenceTriple_isPullback f g i).flip
  have H' : IsPullback
      (correspondenceRightRemainingPairToImageIncidence f g h i z w v t ≫ kL)
      a (pullback.diagonal g) (u ≫ mT) := by
    rw [correspondenceRightRemainingPairToImageIncidence_middle,
      correspondenceRightRemainingSupportToImageExterior_middle]
    exact H.flip
  exact H'.of_right
    (correspondenceRightRemainingPairToImageIncidence_inclusion f g h i z w v t)
    (correspondenceRightImageMiddlePair_isPullback f g h i z w v).flip

/-- The actual remaining point fixes its exact exterior stalk point. -/
theorem correspondenceRightRemainingPairToImageIncidence_point
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t)) :
    correspondenceRightImageIncidenceInclusion f g h i z w v
        (correspondenceRightRemainingPairToImageIncidence f g h i z w v t y) =
      correspondenceRightRemainingSupportToImageExterior f g h i z w v t
        (correspondenceIncidenceToSupportProduct f g i z (correspondenceIncidenceMap g h i w v t)
          y) := by
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun r => r y)
    (correspondenceRightRemainingPairToImageIncidence_inclusion f g h i z w v t)

/-- The full component ideal restricts to the actual closed remaining incidence. -/
theorem correspondenceRightRemainingPairToImageIncidence_ker
    (t : correspondenceIncidence g h i w v) :
    (correspondenceRightRemainingPairToImageIncidence f g h i z w v t).ker =
      (correspondenceRightRemainingImageComponent f g h i z w v t).comap
        (correspondenceRightImageIncidenceInclusion f g h i z w v) := by
  let H := correspondenceRightRemainingPairToImageIncidence_isPullback f g h i z w v t
  rw [← H.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    correspondenceRightRemainingSupportToImageExterior_ker]

/-- A point of the actual remaining pair over a whole-image generic point is generic. -/
theorem mem_genericPoints_correspondenceRightRemainingPair_of_image
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t))
    (hy : correspondenceRightRemainingPairToImageIncidence f g h i z w v t y ∈
      genericPoints (correspondenceRightImageIncidence f g h i z w v)) :
    y ∈ genericPoints (correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t)) :=
  mem_genericPoints_of_mem_genericPoints_image
    (correspondenceRightRemainingPairToImageIncidence f g h i z w v t)
    (correspondenceRightRemainingPairToImageIncidence f g h i z w v t).continuous
    (correspondenceRightRemainingPairToImageIncidence
      f g h i z w v t).isClosedEmbedding.injective hy

end Stacks.Chow
