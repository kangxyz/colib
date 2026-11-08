/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleIncidence
public import Colib.AlgebraicGeometry.Correspondences.Composition.AmbientIntersection
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleDiagonal

/-!
# Actual six-factor and successive-diagonal support geometry

The exterior product of three genuine supports lies in the six-factor ambient
scheme. The first middle diagonal cuts out the pair incidence times the last
support, and the second cuts out the full triple incidence. All maps and
Cartesian squares retain the original scheme structures and their nilpotents.

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Correspondences/Composition/Associativity/DiagonalAmbient.lean,
Git blob 98a35ad930de1c9badf38202fbef1b982cb6db26. The actual supports and
native pullback associator are imported from the selected Colib incidence owner.
The output is a geometric supplier, not a proof of Cor associativity.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Chow
open AlgebraicGeometry.Scheme.Hom

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The full pair incidence times the third support, before the second diagonal. -/
abbrev correspondenceLeftIntermediateSupportProduct : Scheme.{u} :=
  pullback (correspondenceIncidenceRight f g h z w ≫ h)
    (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)

/-- The actual second-diagonal map on the original triple incidence. -/
abbrev correspondenceTripleIncidenceToLeftSupportProduct :
    correspondenceTripleIncidence f g h i z w v ⟶
      correspondenceLeftIntermediateSupportProduct f g h i z w v :=
  pullback.mapDesc (correspondenceIncidenceRight f g h z w)
    ((integralComponentAt v).subschemeι ≫ pullback.fst h i) h

instance isClosedImmersion_correspondenceTripleIncidenceToLeftSupportProduct [IsSeparated h] :
    IsClosedImmersion (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v) := by
  dsimp only [correspondenceTripleIncidenceToLeftSupportProduct]
  infer_instance

@[reassoc (attr := simp)]
theorem correspondenceTripleIncidenceToLeftSupportProduct_fst :
    correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v ≫
      pullback.fst _ _ = correspondenceTripleIncidenceFst f g h i z w v := by
  simp only [correspondenceTripleIncidenceToLeftSupportProduct, pullback.mapDesc, pullback.map,
    pullback.lift_fst, Category.comp_id]

/-- The last coordinate of the actual first two support factors. -/
abbrev correspondenceSupportProductTarget : (correspondenceSupportProduct f g h z w) ⟶ Z :=
  pullback.snd ((integralComponentAt z).subschemeι ≫ pullback.snd f g ≫ g)
    ((integralComponentAt w).subschemeι ≫ pullback.fst g h ≫ g) ≫ ((integralComponentAt
    w).subschemeι ≫ pullback.snd g h)

/-- The genuine exterior product of all three support schemes. -/
abbrev correspondenceTripleSupportProduct : Scheme.{u} :=
  pullback ((correspondenceSupportProductTarget f g h z w) ≫ h) (((integralComponentAt
    v).subschemeι ≫ pullback.fst h i) ≫ h)

/-- The actual exterior support inclusion into the six-factor ambient. -/
def correspondenceTripleSupportProductInclusion : (correspondenceTripleSupportProduct f g h i z w
  v) ⟶
    correspondenceSixfoldAmbient f g h i :=
  pullback.map _ _ _ _ (correspondenceSupportProductInclusion f g h z w) (integralComponentAt
    v).subschemeι (𝟙 S)
    (by simp [correspondenceSupportProductTarget, correspondenceAmbientTarget])
    (by simp)

set_option backward.isDefEq.respectTransparency false in
instance : IsClosedImmersion (correspondenceTripleSupportProductInclusion f g h i z w v) := by
  unfold correspondenceTripleSupportProductInclusion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion (correspondenceSupportProductInclusion f g h z w)))
    (inferInstanceAs (IsClosedImmersion (integralComponentAt v).subschemeι))
    (by simp [correspondenceSupportProductTarget, correspondenceAmbientTarget])
    (by simp)

/-- The genuine first-stage support embeds in the first-diagonal ambient. -/
def correspondenceLeftIntermediateSupportInclusion : (correspondenceLeftIntermediateSupportProduct
  f g h i z w v) ⟶
    correspondenceFirstDiagonal f g h i :=
  pullback.map _ _ _ _ (correspondenceIncidenceInclusion f g h z w) (integralComponentAt
    v).subschemeι (𝟙 S)
    (by simp [correspondenceIncidenceRight, correspondenceTripleTarget])
    (by simp)

set_option backward.isDefEq.respectTransparency false in
instance : IsClosedImmersion (correspondenceLeftIntermediateSupportInclusion f g h i z w v) := by
  unfold correspondenceLeftIntermediateSupportInclusion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion (correspondenceIncidenceInclusion f g h z w)))
    (inferInstanceAs (IsClosedImmersion (integralComponentAt v).subschemeι))
    (by simp [correspondenceIncidenceRight, correspondenceTripleTarget])
    (by simp)

/-- First-stage support maps to the original exterior coefficient support. -/
def correspondenceLeftIntermediateToTripleSupport : (correspondenceLeftIntermediateSupportProduct
  f g h i z w v) ⟶
    (correspondenceTripleSupportProduct f g h i z w v) :=
  pullback.map _ _ _ _ (correspondenceIncidenceToSupportProduct f g h z w) (𝟙 (integralComponentAt
    v).subscheme) (𝟙 S)
    (by simp [correspondenceIncidenceRight, correspondenceSupportProductTarget]) (by simp)

/-- Exterior support inclusion on its first pair. -/
@[reassoc (attr := simp)] theorem correspondenceTripleSupportProductInclusion_fst :
    (correspondenceTripleSupportProductInclusion f g h i z w v) ≫
      pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.fst ((correspondenceSupportProductTarget f g h z w) ≫ h) (((integralComponentAt
      v).subschemeι ≫ pullback.fst h i) ≫ h) ≫
      (correspondenceSupportProductInclusion f g h z w) := pullback.lift_fst _ _ _

/-- Exterior support inclusion on its last support. -/
@[reassoc (attr := simp)] theorem correspondenceTripleSupportProductInclusion_snd :
    (correspondenceTripleSupportProductInclusion f g h i z w v) ≫
      pullback.snd (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.snd ((correspondenceSupportProductTarget f g h z w) ≫ h) (((integralComponentAt
      v).subschemeι ≫ pullback.fst h i) ≫ h) ≫ (integralComponentAt v).subschemeι :=
  pullback.lift_snd _ _ _

/-- First-stage support inclusion on its incidence factor. -/
@[reassoc (attr := simp)] theorem correspondenceLeftIntermediateSupportInclusion_fst :
    (correspondenceLeftIntermediateSupportInclusion f g h i z w v) ≫
      pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.fst ((correspondenceIncidenceRight f g h z w) ≫ h) (((integralComponentAt
      v).subschemeι ≫ pullback.fst h i) ≫ h) ≫ (correspondenceIncidenceInclusion f g h z w) :=
  pullback.lift_fst _ _ _

/-- First-stage support inclusion on its last support. -/
@[reassoc (attr := simp)] theorem correspondenceLeftIntermediateSupportInclusion_snd :
    (correspondenceLeftIntermediateSupportInclusion f g h i z w v) ≫
      pullback.snd (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h) =
    pullback.snd ((correspondenceIncidenceRight f g h z w) ≫ h) (((integralComponentAt
      v).subschemeι ≫ pullback.fst h i) ≫ h) ≫ (integralComponentAt v).subschemeι :=
  pullback.lift_snd _ _ _

/-- The map to the coefficient support keeps the actual pair-to-product map. -/
@[reassoc (attr := simp)] theorem correspondenceLeftIntermediateToTripleSupport_fst :
    (correspondenceLeftIntermediateToTripleSupport f g h i z w v) ≫
      pullback.fst ((correspondenceSupportProductTarget f g h z w) ≫ h) (((integralComponentAt
        v).subschemeι ≫ pullback.fst h i) ≫ h) =
    pullback.fst ((correspondenceIncidenceRight f g h z w) ≫ h) (((integralComponentAt
      v).subschemeι ≫ pullback.fst h i) ≫ h) ≫
      (correspondenceIncidenceToSupportProduct f g h z w) := pullback.lift_fst _ _ _

/-- The map to the coefficient support keeps the third support unchanged. -/
@[reassoc (attr := simp)] theorem correspondenceLeftIntermediateToTripleSupport_snd :
    (correspondenceLeftIntermediateToTripleSupport f g h i z w v) ≫
      pullback.snd ((correspondenceSupportProductTarget f g h z w) ≫ h) (((integralComponentAt
        v).subschemeι ≫ pullback.fst h i) ≫ h) =
    pullback.snd ((correspondenceIncidenceRight f g h z w) ≫ h) (((integralComponentAt
      v).subschemeι ≫ pullback.fst h i) ≫ h) := by
  simp only [correspondenceLeftIntermediateToTripleSupport, pullback.map, pullback.lift_snd,
    Category.comp_id]

/-- Both first-stage maps give the same actual six-factor ambient morphism. -/
@[reassoc] theorem correspondenceLeftIntermediate_ambient_comm :
    (correspondenceLeftIntermediateSupportInclusion f g h i z w v) ≫
      correspondenceFirstDiagonalInclusion f g h i =
    (correspondenceLeftIntermediateToTripleSupport f g h i z w v) ≫
      (correspondenceTripleSupportProductInclusion f g h i z w v) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, correspondenceFirstDiagonalInclusion_fst,
      correspondenceLeftIntermediateSupportInclusion_fst_assoc,
        correspondenceTripleSupportProductInclusion_fst,
      correspondenceLeftIntermediateToTripleSupport_fst_assoc, correspondenceIncidence_ambient_comm]
  · simp

/-- The first diagonal and the exterior coefficient support have exactly the
actual pair-incidence-times-third-support scheme as Cartesian intersection. -/
theorem correspondenceLeftIntermediate_ambient_isPullback :
    IsPullback (correspondenceLeftIntermediateSupportInclusion f g h i z w v)
      (correspondenceLeftIntermediateToTripleSupport f g h i z w v)
      (correspondenceFirstDiagonalInclusion f g h i) (correspondenceTripleSupportProductInclusion
        f g h i z w v) where
  w := (correspondenceLeftIntermediate_ambient_comm f g h i z w v)
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun c ↦ by
    have ha := congrArg (fun m => m ≫
      pullback.fst (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)) c.condition
    have hb := congrArg (fun m => m ≫
      pullback.snd (correspondenceAmbientTarget f g h ≫ h) (pullback.fst h i ≫ h)) c.condition
    simp only [Category.assoc, correspondenceFirstDiagonalInclusion_fst,
      correspondenceTripleSupportProductInclusion_fst] at ha
    simp only [Category.assoc, correspondenceFirstDiagonalInclusion_snd,
      correspondenceTripleSupportProductInclusion_snd] at hb
    let pairLift : c.pt ⟶ (correspondenceIncidence f g h z w) :=
      ((isPullback_correspondenceAmbientIncidence f g h z w)).lift
      (c.fst ≫ pullback.fst _ _) (c.snd ≫ pullback.fst _ _) (by
        simpa only [Category.assoc] using ha)
    have hv₁ : pairLift ≫ (correspondenceIncidenceInclusion f g h z w) = c.fst ≫ pullback.fst _ _ :=
      IsPullback.lift_fst _ _ _ _
    have hv₂ : pairLift ≫ (correspondenceIncidenceToSupportProduct f g h z w) = c.snd ≫
      pullback.fst _ _ :=
      IsPullback.lift_snd _ _ _ _
    have hbase : pairLift ≫ ((correspondenceIncidenceRight f g h z w) ≫ h) =
        (c.snd ≫ pullback.snd ((correspondenceSupportProductTarget f g h z w) ≫ h)
          (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)) ≫
          (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) := by
      calc
        _ = (pairLift ≫ (correspondenceIncidenceToSupportProduct f g h z w)) ≫
          ((correspondenceSupportProductTarget f g h z w) ≫ h) := by
          simp [correspondenceSupportProductTarget, correspondenceIncidenceRight]
        _ = (c.snd ≫ pullback.fst _ _) ≫ ((correspondenceSupportProductTarget f g h z w) ≫ h) :=
          by rw [hv₂]
        _ = _ := by
          simpa only [Category.assoc] using congrArg (c.snd ≫ ·)
            (pullback.condition (f := (correspondenceSupportProductTarget f g h z w) ≫ h) (g :=
              ((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h))
    let tripleLift : c.pt ⟶ (correspondenceLeftIntermediateSupportProduct f g h i z w v) :=
      pullback.lift pairLift (c.snd ≫ pullback.snd _ _) hbase
    have hw₁ : tripleLift ≫ (correspondenceLeftIntermediateSupportInclusion f g h i z w v) = c.fst
      := by
      apply pullback.hom_ext
      · simpa only [Category.assoc, correspondenceLeftIntermediateSupportInclusion_fst,
          tripleLift, pullback.lift_fst_assoc] using hv₁
      · simpa only [Category.assoc, correspondenceLeftIntermediateSupportInclusion_snd,
          tripleLift, pullback.lift_snd_assoc] using hb.symm
    have hw₂ : tripleLift ≫ (correspondenceLeftIntermediateToTripleSupport f g h i z w v) = c.snd
      := by
      apply pullback.hom_ext
      · simpa only [Category.assoc, correspondenceLeftIntermediateToTripleSupport_fst,
          tripleLift, pullback.lift_fst_assoc] using hv₂
      · simp only [Category.assoc, correspondenceLeftIntermediateToTripleSupport_snd,
          tripleLift, pullback.lift_snd]
    refine ⟨tripleLift, hw₁, hw₂, ?_⟩
    intro m hm _
    exact (cancel_mono (correspondenceLeftIntermediateSupportInclusion f g h i z w v)).mp
      (hm.trans hw₁.symm))⟩

/-- The first-stage ambient map keeps the entire original scheme structure. -/
abbrev correspondenceLeftIntermediateAmbientInclusion :
  (correspondenceLeftIntermediateSupportProduct f g h i z w v) ⟶
    correspondenceSixfoldAmbient f g h i :=
  (correspondenceLeftIntermediateSupportInclusion f g h i z w v) ≫
    correspondenceFirstDiagonalInclusion f g h i

instance [IsSeparated g] : IsClosedImmersion (correspondenceLeftIntermediateAmbientInclusion f g h
  i z w v) :=
  inferInstanceAs (IsClosedImmersion
    ((correspondenceLeftIntermediateSupportInclusion f g h i z w v) ≫
      correspondenceFirstDiagonalInclusion f g h i))

/-- The first-stage ideal is the sum of the actual first-diagonal and exterior
coefficient ideals, preserving nilpotents and all embedded support. -/
theorem correspondenceLeftIntermediateAmbientInclusion_ker [IsSeparated g] :
    (correspondenceLeftIntermediateAmbientInclusion f g h i z w v).ker =
      (correspondenceFirstDiagonalInclusion f g h i).ker ⊔
        (correspondenceTripleSupportProductInclusion f g h i z w v).ker :=
  ker_comp_eq_sup_of_isPullback _ _ _ _ (correspondenceLeftIntermediate_ambient_isPullback f g h i
    z w v)

/-- Actual triple incidence embeds in the fourfold product using its original
pair-incidence and third-support coordinates. -/
def correspondenceTripleIncidenceFourfoldInclusion : (correspondenceTripleIncidence f g h i z w v) ⟶
    correspondenceFourfoldProduct f g h i :=
  pullback.map _ _ _ _ (correspondenceIncidenceInclusion f g h z w) (integralComponentAt
    v).subschemeι (𝟙 Z)
    (by simp [correspondenceIncidenceRight, correspondenceTripleTarget])
    (by simp)

set_option backward.isDefEq.respectTransparency false in
instance : IsClosedImmersion (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v) := by
  unfold correspondenceTripleIncidenceFourfoldInclusion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion (correspondenceIncidenceInclusion f g h z w)))
    (inferInstanceAs (IsClosedImmersion (integralComponentAt v).subschemeι))
    (by simp [correspondenceIncidenceRight, correspondenceTripleTarget])
    (by simp)

/-- The actual fourfold inclusion preserves the original pair-incidence coordinate. -/
@[reassoc (attr := simp)] theorem correspondenceTripleIncidenceFourfoldInclusion_fst :
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v) ≫
      pullback.fst (correspondenceTripleTarget f g h) (pullback.fst h i) =
    (correspondenceTripleIncidenceFst f g h i z w v) ≫ (correspondenceIncidenceInclusion f g h z
      w) := pullback.lift_fst _ _ _

/-- The actual fourfold inclusion preserves the original third-support coordinate. -/
@[reassoc (attr := simp)] theorem correspondenceTripleIncidenceFourfoldInclusion_snd :
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v) ≫
      pullback.snd (correspondenceTripleTarget f g h) (pullback.fst h i) =
    (correspondenceTripleIncidenceSnd f g h i z w v) ≫ (integralComponentAt v).subschemeι :=
      pullback.lift_snd _ _ _

/-- The remaining-diagonal support embedding keeps the original third support. -/
@[reassoc (attr := simp)] theorem correspondenceTripleIncidenceToLeftSupportProduct_snd :
    (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v) ≫
      pullback.snd ((correspondenceIncidenceRight f g h z w) ≫ h) (((integralComponentAt
        v).subschemeι ≫ pullback.fst h i) ≫ h) =
    (correspondenceTripleIncidenceSnd f g h i z w v) := by
  simp only [correspondenceTripleIncidenceToLeftSupportProduct, pullback.mapDesc, pullback.map,
    pullback.lift_snd, Category.comp_id, correspondenceTripleIncidenceSnd]

/-- The remaining diagonal and the genuine first-stage support give the same
ambient morphism on actual triple incidence. -/
@[reassoc] theorem correspondenceTripleIncidence_firstDiagonal_comm :
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v) ≫
      correspondenceSecondDiagonalInclusion f g h i =
    (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v) ≫
      (correspondenceLeftIntermediateSupportInclusion f g h i z w v) := by
  apply pullback.hom_ext <;> simp

/-- The remaining diagonal cuts out exactly the full actual triple-incidence
scheme from the first-stage support product. -/
theorem correspondenceTripleIncidence_firstDiagonal_isPullback :
    IsPullback (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v)
      (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v)
      (correspondenceSecondDiagonalInclusion f g h i)
      (correspondenceLeftIntermediateSupportInclusion f g h i z w v) where
  w := (correspondenceTripleIncidence_firstDiagonal_comm f g h i z w v)
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun c ↦ by
    have ha := congrArg (fun m => m ≫
      pullback.fst (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h)) c.condition
    have hb := congrArg (fun m => m ≫
      pullback.snd (correspondenceTripleTarget f g h ≫ h) (pullback.fst h i ≫ h)) c.condition
    simp only [Category.assoc, correspondenceSecondDiagonalInclusion, pullback.mapDesc,
      pullback.map, pullback.lift_fst, Category.comp_id,
      correspondenceLeftIntermediateSupportInclusion_fst] at ha
    simp only [Category.assoc, correspondenceSecondDiagonalInclusion, pullback.mapDesc,
      pullback.map, pullback.lift_snd, Category.comp_id,
      correspondenceLeftIntermediateSupportInclusion_snd] at hb
    have hbase :
        (c.snd ≫ pullback.fst ((correspondenceIncidenceRight f g h z w) ≫ h)
          (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)) ≫
          (correspondenceIncidenceRight f g h z w) =
        (c.snd ≫ pullback.snd ((correspondenceIncidenceRight f g h z w) ≫ h)
          (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)) ≫ ((integralComponentAt
          v).subschemeι ≫ pullback.fst h i) := by
      calc
        _ = (c.snd ≫ pullback.fst _ _ ≫ (correspondenceIncidenceInclusion f g h z w)) ≫
            correspondenceTripleTarget f g h := by
          simp [correspondenceTripleTarget, correspondenceIncidenceRight]
        _ = (c.fst ≫ pullback.fst _ _) ≫ correspondenceTripleTarget f g h := by rw [ha]
        _ = (c.fst ≫ pullback.snd _ _) ≫ pullback.fst h i := by
          simp only [Category.assoc, pullback.condition]
        _ = _ := by rw [hb]; rfl
    let tripleLift : c.pt ⟶ (correspondenceTripleIncidence f g h i z w v) :=
      pullback.lift (c.snd ≫ pullback.fst _ _) (c.snd ≫ pullback.snd _ _) hbase
    have hw₁ : tripleLift ≫ (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v) = c.fst
      := by
      apply pullback.hom_ext
      · simpa only [Category.assoc, correspondenceTripleIncidenceFourfoldInclusion_fst,
          correspondenceTripleIncidenceFst, tripleLift, pullback.lift_fst_assoc] using ha.symm
      · simpa only [Category.assoc, correspondenceTripleIncidenceFourfoldInclusion_snd,
          correspondenceTripleIncidenceSnd, tripleLift, pullback.lift_snd_assoc] using hb.symm
    have hw₂ : tripleLift ≫ (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v) =
      c.snd := by
      apply pullback.hom_ext
      · simp only [Category.assoc, tripleLift, pullback.lift_fst, Category.comp_id]
      · simp only [Category.assoc, tripleLift, pullback.lift_snd, Category.comp_id]
    refine ⟨tripleLift, hw₁, hw₂, ?_⟩
    intro m hm _
    exact (cancel_mono (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v)).mp
      (hm.trans hw₁.symm))⟩

/-- The complete triple-incidence embedding into the six-factor ambient. -/
abbrev correspondenceTripleIncidenceSixfoldInclusion : (correspondenceTripleIncidence f g h i z w
  v) ⟶
    correspondenceSixfoldAmbient f g h i :=
  (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v) ≫
    correspondenceSecondDiagonalInclusion f g h i ≫ correspondenceFirstDiagonalInclusion f g h i

instance [IsSeparated g] [IsSeparated h] :
    IsClosedImmersion (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v) :=
  inferInstanceAs (IsClosedImmersion ((correspondenceTripleIncidenceFourfoldInclusion f g h i z w
    v) ≫
    correspondenceSecondDiagonalInclusion f g h i ≫ correspondenceFirstDiagonalInclusion f g h i))

/-- The full actual triple incidence is the Cartesian intersection of the
combined two diagonals with the original exterior coefficient support. -/
theorem correspondenceTripleIncidence_sixfold_isPullback :
    IsPullback (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v)
      ((correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v) ≫
        (correspondenceLeftIntermediateToTripleSupport f g h i z w v))
      (correspondenceSecondDiagonalInclusion f g h i ≫ correspondenceFirstDiagonalInclusion f g h i)
      (correspondenceTripleSupportProductInclusion f g h i z w v) :=
  (correspondenceTripleIncidence_firstDiagonal_isPullback f g h i z w v).paste_vert
    (correspondenceLeftIntermediate_ambient_isPullback f g h i z w v)

/-- In the first-diagonal ambient the full actual triple ideal is the sum
of the remaining diagonal ideal and the first-stage support ideal. -/
theorem correspondenceTripleIncidenceFirstDiagonalInclusion_ker [IsSeparated h] :
    ((correspondenceTripleIncidenceFourfoldInclusion f g h i z w v) ≫
      correspondenceSecondDiagonalInclusion f g h i).ker =
      (correspondenceSecondDiagonalInclusion f g h i).ker ⊔
        (correspondenceLeftIntermediateSupportInclusion f g h i z w v).ker :=
  ker_comp_eq_sup_of_isPullback _ _ _ _ (correspondenceTripleIncidence_firstDiagonal_isPullback f
    g h i z w v)

/-- The actual six-factor triple ideal retains the combined diagonal ideal
and the original exterior coefficient ideal, without passing to reductions. -/
theorem correspondenceTripleIncidenceSixfoldInclusion_ker [IsSeparated g] [IsSeparated h] :
    (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v).ker =
      (correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i).ker ⊔
          (correspondenceTripleSupportProductInclusion f g h i z w v).ker :=
  ker_comp_eq_sup_of_isPullback _ _ _ _ (correspondenceTripleIncidence_sixfold_isPullback f g h i
    z w v)

/-- The full triple incidence is cut out by the two middle diagonal ideals and the
original exterior-support ideal, with no radical and no flat-support premise. -/
theorem correspondenceTripleIncidenceSixfoldInclusion_ker_eq_threeIdeals
    [IsSeparated g] [IsSeparated h] :
    (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v).ker =
      (correspondenceFirstDiagonalInclusion f g h i).ker ⊔
        ((correspondenceSecondAmbientInclusion f g h i).ker ⊔
          (correspondenceTripleSupportProductInclusion f g h i z w v).ker) := by
  rw [correspondenceTripleIncidenceSixfoldInclusion_ker,
    ker_correspondenceFourfoldDiagonal, sup_assoc]

/-- The full actual triple-incidence scheme is the native subscheme of the sum ideal. -/
def correspondenceTripleIncidenceThreeIdealIso [IsSeparated g] [IsSeparated h] :
    correspondenceTripleIncidence f g h i z w v ≅
      ((correspondenceFirstDiagonalInclusion f g h i).ker ⊔
        ((correspondenceSecondAmbientInclusion f g h i).ker ⊔
          (correspondenceTripleSupportProductInclusion f g h i z w v).ker)).subscheme :=
  asIso (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v).toImage ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme
      (correspondenceTripleIncidenceSixfoldInclusion_ker_eq_threeIdeals f g h i z w v))

end Stacks.Chow
