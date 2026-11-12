/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleCurveOriginalSectionStages

/-! # Original retained-section targets at every small curve stage

The target map lives only on the retained source. No extension across the compactification
is assumed. All recovery equalities are whole scheme-morphism equalities.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N Y : Scheme.{u}} (p : N ⟶ X.left) (j : Y ⟶ N)
  (σY : X.left ⟶ Y)

/-- The literal retained curve over the actual affine neighborhood. -/
abbrev etaleCurveOriginalRetainedStage (i : SmallEtaleNeighborhood X s) :=
  pullback ((smallEtaleNeighborhoodOver X s).obj i).hom (j ≫ p)

/-- Its actual inclusion into the whole compactified stage. -/
def etaleCurveOriginalRetainedStageMap (i : SmallEtaleNeighborhood X s) :
    etaleCurveOriginalRetainedStage X s p j i ⟶ (etaleCurveDiagram X s p).obj i :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ j)
    (pullback.condition.trans (Category.assoc _ j p).symm)

/-- The original retained section pulls back without extending its target map. -/
def etaleCurveOriginalRetainedSectionStage (hσY : σY ≫ (j ≫ p) = 𝟙 _)
    (i : SmallEtaleNeighborhood X s) :
    (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶
      etaleCurveOriginalRetainedStage X s p j i :=
  pullback.lift (𝟙 (((smallEtaleNeighborhoodOver X s).obj i).left))
    (((smallEtaleNeighborhoodOver X s).obj i).hom ≫ σY)
    ((Category.id_comp _).trans
      ((Category.assoc ((smallEtaleNeighborhoodOver X s).obj i).hom σY (j ≫ p)).trans
        ((congrArg (fun z : X.left ⟶ X.left =>
          ((smallEtaleNeighborhoodOver X s).obj i).hom ≫ z) hσY).trans
          (Category.comp_id _))).symm)

variable (hσY : σY ≫ (j ≫ p) = 𝟙 _) (i : SmallEtaleNeighborhood X s)

/-- The retained lift is the exact original whole-section stage. -/
theorem etaleCurveOriginalRetainedSectionStage_whole :
    etaleCurveOriginalRetainedSectionStage X s p j σY hσY i ≫
        etaleCurveOriginalRetainedStageMap X s p j i =
      etaleCurveOriginalSectionStage X s p (σY ≫ j)
        ((Category.assoc σY j p).trans hσY) i := by
  let Aᵢ : Scheme := ((smallEtaleNeighborhoodOver X s).obj i).left
  let g : Aᵢ ⟶ X.left := ((smallEtaleNeighborhoodOver X s).obj i).hom
  let Cᵢ : Scheme := pullback g p
  let Yᵢ : Scheme := pullback g (j ≫ p)
  let u : Aᵢ ⟶ Yᵢ := etaleCurveOriginalRetainedSectionStage X s p j σY hσY i
  let v : Yᵢ ⟶ Cᵢ := etaleCurveOriginalRetainedStageMap X s p j i
  let w : Aᵢ ⟶ Cᵢ := etaleCurveOriginalSectionStage X s p (σY ≫ j)
    ((Category.assoc σY j p).trans hσY) i
  have hv₁ : v ≫ pullback.fst g p = pullback.fst g (j ≫ p) :=
    pullback.lift_fst _ _ _
  have hv₂ : v ≫ pullback.snd g p = pullback.snd g (j ≫ p) ≫ j :=
    pullback.lift_snd _ _ _
  have hu₁ : u ≫ pullback.fst g (j ≫ p) = 𝟙 Aᵢ := pullback.lift_fst _ _ _
  have hu₂ : u ≫ pullback.snd g (j ≫ p) = g ≫ σY := pullback.lift_snd _ _ _
  have hw₁ : w ≫ pullback.fst g p = 𝟙 Aᵢ :=
    etaleCurveOriginalSectionStage_projection X s p (σY ≫ j) _ i
  have hw₂ : w ≫ pullback.snd g p = g ≫ (σY ≫ j) :=
    etaleCurveOriginalSectionStage_original X s p (σY ≫ j) _ i
  have h₁ : (u ≫ v) ≫ pullback.fst g p = w ≫ pullback.fst g p :=
    (Category.assoc u v _).trans
      ((congrArg (fun z : Yᵢ ⟶ Aᵢ => u ≫ z) hv₁).trans (hu₁.trans hw₁.symm))
  have h₂ : (u ≫ v) ≫ pullback.snd g p = w ≫ pullback.snd g p :=
    (Category.assoc u v _).trans
      ((congrArg (fun z : Yᵢ ⟶ N => u ≫ z) hv₂).trans
        ((Category.assoc u (pullback.snd g (j ≫ p)) j).symm.trans
          ((congrArg (fun z : Aᵢ ⟶ Y => z ≫ j) hu₂).trans
            ((Category.assoc g σY j).trans hw₂.symm))))
  exact pullback.hom_ext h₁ h₂

/-- Only the original retained map is used to recover the original restriction target. -/
@[reassoc]
theorem etaleCurveOriginalRetainedSectionStage_target {T : Scheme.{u}} (t : Y ⟶ T) :
    etaleCurveOriginalRetainedSectionStage X s p j σY hσY i ≫
        (pullback.snd ((smallEtaleNeighborhoodOver X s).obj i).hom (j ≫ p) ≫ t) =
      (etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i)).left ≫
        (σY ≫ t) := by
  let Aᵢ : Scheme := ((smallEtaleNeighborhoodOver X s).obj i).left
  let g : Aᵢ ⟶ X.left := ((smallEtaleNeighborhoodOver X s).obj i).hom
  let Yᵢ : Scheme := pullback g (j ≫ p)
  let u : Aᵢ ⟶ Yᵢ := etaleCurveOriginalRetainedSectionStage X s p j σY hσY i
  have hu : u ≫ pullback.snd g (j ≫ p) = g ≫ σY := pullback.lift_snd _ _ _
  exact (Category.assoc u (pullback.snd g (j ≫ p)) t).symm.trans
    ((congrArg (fun z : Aᵢ ⟶ Y => z ≫ t) hu).trans (Category.assoc g σY t))

end AlgebraicGeometry.Scheme.SmoothSite
