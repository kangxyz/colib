/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageComponentStalk
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingPrimeTorComparison
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.GenericPoints

/-!
# The original remaining pair inside the whole image incidence

The original image point is kept literally. The closed map of its full support product to
the whole image exterior induces a map of the actual remaining incidences by the native
diagonal pullback. The square is proved Cartesian. Its stalk points and its full ideal
are consequently determined by actual scheme maps, not supplied coefficient comparisons.
This does not assert admissibility of the original image point.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) (t : correspondenceIncidence f g h z w)

local notation3 (prettyPrint := false) "q" => correspondenceIncidenceMap f g h z w t
local notation3 (prettyPrint := false) "P" => correspondenceSupportProduct f h i q v
local notation3 (prettyPrint := false) "N" => correspondenceIncidence f h i q v
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "L" => correspondenceLeftImageIncidence f g h i z w v
local notation3 (prettyPrint := false) "u" =>
  correspondenceRemainingSupportToImageExterior f g h i z w v t
local notation3 (prettyPrint := false) "a" => correspondenceIncidenceToSupportProduct f h i q v
local notation3 (prettyPrint := false) "b" => correspondenceIncidenceInclusion f h i q v
local notation3 (prettyPrint := false) "j" => correspondenceLeftImageProductInclusion f g h i z w v
local notation3 (prettyPrint := false) "ι" => correspondenceSupportProductInclusion f h i q v
local notation3 (prettyPrint := false) "d" => correspondenceTripleInclusion f h i
local notation3 (prettyPrint := false) "m" => correspondenceMiddlePair f h i
local notation3 (prettyPrint := false) "mT" => correspondenceLeftImageMiddlePair f g h i z w v
local notation3 (prettyPrint := false) "jL" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v
local notation3 (prettyPrint := false) "k" => correspondenceTripleMiddle f h i
local notation3 (prettyPrint := false) "kL" =>
  pullback.fst (correspondenceIntermediateImageTarget f g h z w)
    ((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫
      correspondenceIntermediateImageTarget f g h z w

/-- The original remaining support keeps the original remaining middle pair. -/
@[reassoc]
theorem correspondenceRemainingSupportToImageExterior_middle : u ≫ mT = ι ≫ m := by
  rw [← correspondenceLeftImageProductInclusion_middlePair f g h i z w v,
    ← Category.assoc, correspondenceRemainingSupportToImageExterior_ambient]

private theorem correspondenceRemainingPairImage_condition :
    (a ≫ u) ≫ mT = (b ≫ k) ≫ pullback.diagonal h := by
  rw [Category.assoc, correspondenceRemainingSupportToImageExterior_middle,
    ← Category.assoc, ← correspondenceIncidence_ambient_comm]
  simpa only [Category.assoc] using
    congrArg (fun r => b ≫ r) (correspondenceTriple_isPullback f h i).w.symm

/-- The actual original remaining pair maps to the incidence of the whole intermediate image. -/
def correspondenceRemainingPairToImageIncidence : N ⟶ L :=
  (correspondenceLeftImageMiddlePair_isPullback f g h i z w v).lift
    (a ≫ u) (b ≫ k) (correspondenceRemainingPairImage_condition f g h i z w v t)

/-- The full remaining support point is preserved by the actual incidence map. -/
@[reassoc]
theorem correspondenceRemainingPairToImageIncidence_inclusion :
    correspondenceRemainingPairToImageIncidence f g h i z w v t ≫ jL = a ≫ u := by
  apply IsPullback.lift_fst

/-- The diagonal point is preserved by the actual incidence map. -/
@[reassoc]
theorem correspondenceRemainingPairToImageIncidence_middle :
    correspondenceRemainingPairToImageIncidence f g h i z w v t ≫ kL = b ≫ k := by
  apply IsPullback.lift_snd

/-- This is the genuine base change of the full component support embedding. -/
theorem correspondenceRemainingPairToImageIncidence_isPullback :
    IsPullback (correspondenceRemainingPairToImageIncidence f g h i z w v t)
      a jL u := by
  have H := (isPullback_correspondenceAmbientIncidence f h i q v).flip.paste_vert
    (correspondenceTriple_isPullback f h i).flip
  have H' : IsPullback
      (correspondenceRemainingPairToImageIncidence f g h i z w v t ≫ kL)
      a (pullback.diagonal h) (u ≫ mT) := by
    rw [correspondenceRemainingPairToImageIncidence_middle,
      correspondenceRemainingSupportToImageExterior_middle]
    exact H.flip
  exact H'.of_right
    (correspondenceRemainingPairToImageIncidence_inclusion f g h i z w v t)
    (correspondenceLeftImageMiddlePair_isPullback f g h i z w v).flip

instance isClosedImmersion_correspondenceRemainingPairToImageIncidence :
    IsClosedImmersion (correspondenceRemainingPairToImageIncidence f g h i z w v t) :=
  MorphismProperty.of_isPullback
    (correspondenceRemainingPairToImageIncidence_isPullback f g h i z w v t).flip inferInstance

/-- The original incidence label determines the exact whole-image exterior stalk point. -/
theorem correspondenceRemainingPairToImageIncidence_point (y : N) :
    jL (correspondenceRemainingPairToImageIncidence f g h i z w v t y) = u (a y) := by
  simpa only [Scheme.Hom.comp_apply] using
    congrArg (fun r => r y)
      (correspondenceRemainingPairToImageIncidence_inclusion f g h i z w v t)

/-- The full component ideal restricts to the actual closed remaining-pair incidence. -/
theorem correspondenceRemainingPairToImageIncidence_ker :
    (correspondenceRemainingPairToImageIncidence f g h i z w v t).ker =
      (correspondenceRemainingImageComponent f g h i z w v t).comap jL := by
  let H := correspondenceRemainingPairToImageIncidence_isPullback f g h i z w v t
  rw [← H.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    correspondenceRemainingSupportToImageExterior_ker]

/-- A remaining pair point over a whole-image generic point is itself a genuine generic label. -/
theorem mem_genericPoints_correspondenceRemainingPair_of_image (y : N)
    (hy : correspondenceRemainingPairToImageIncidence f g h i z w v t y ∈
      genericPoints L) : y ∈ genericPoints N :=
  mem_genericPoints_of_mem_genericPoints_image
    (correspondenceRemainingPairToImageIncidence f g h i z w v t)
    (correspondenceRemainingPairToImageIncidence f g h i z w v t).continuous
    (correspondenceRemainingPairToImageIncidence f g h i z w v t).isClosedEmbedding.injective hy

end Stacks.Chow
