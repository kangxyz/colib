/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.A1BaseChange

/-! # Actual puncture and native-cylinder base-change compatibility -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/Boundary/Contraction/ProjectionExcisionGeometry.lean`, blob
`658ae71e7f064cc3716386a67a91d0d7e1366604`.
Only the original Product section is extracted. No normal-chart product,
support comparison or canonical boundary epimorphism is used.
Source candidate only; no elaboration result is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

section Product

variable {R : CommRingCat.{u}} {U E : SmoothSite (Spec R)} (j : U ⟶ E)

local notation "T" => SmoothSite.additiveGroupObject (Spec R)
local notation "πE" => NatTrans.app (projection T) E
local notation "πU" => NatTrans.app (projection T) U
local notation "j₁" => affineLineCylinder.map j

/-- The literal product square of a puncture commutes on actual neighborhood
pullbacks, without any coefficient inverse-image comparison. -/
def a1PunctureProjectionBaseChangeIso :
    baseChange (πE).left ⋙
        baseChange (j₁).left ≅
      baseChange j.left ⋙ baseChange (πU).left :=
  (MorphismProperty.Over.pullbackComp (P := etaleSeparatedFiniteType) (Q := ⊤)
    (j₁).left (πE).left).symm ≪≫
    MorphismProperty.Over.pullbackComp (πU).left j.left
      (fg := (j₁ ≫ (projection T).app E).left)
      (hfg := congrArg (fun f ↦ f.left) ((projection T).naturality j))

/-- The product-puncture comparison retains the original ambient projection. -/
@[reassoc (attr := simp)]
theorem a1PunctureProjectionBaseChangeIso_fst (V : EtaleSeparatedFiniteType E.left) :
    ((a1PunctureProjectionBaseChangeIso j).hom.app V).left ≫
        pullback.fst (pullback.snd V.hom j.left) (πU).left ≫
        pullback.fst V.hom j.left =
      pullback.fst (pullback.snd V.hom (πE).left)
          (j₁).left ≫
        pullback.fst V.hom (πE).left := by
  simp only [a1PunctureProjectionBaseChangeIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    MorphismProperty.Comma.comp_left, Category.assoc,
    MorphismProperty.Over.pullbackComp_hom_app_left,
    MorphismProperty.Over.pullbackComp_inv_app_left]
  erw [pullbackLeftPullbackSndIso_inv_fst V.hom j.left (πU).left]
  simp only [pullback.map, pullback.lift_fst, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_fst]

/-- The actual puncture restriction commutes with the original base-change to
cylinder comparison. This is an equality of the specified geometric maps, not
an identification of coefficient inverse images. -/
theorem a1PunctureProjectionBaseChangeIso_restriction (V : EtaleSeparatedFiniteType E.left) :
    (restrictionProjection (affineLineCylinder.map j)).app
        ((baseChange (πE).left).obj V) ≫
        (a1BaseChangeIso R E V).hom =
      (toSmoothSite (affineLineCylinder.obj U)).map
          ((a1PunctureProjectionBaseChangeIso j).hom.app V) ≫
        (a1BaseChangeIso R U ((baseChange j.left).obj V)).hom ≫
        affineLineCylinder.map ((restrictionProjection j).app V) := by
  apply SmoothSite.product_hom_ext
  · have hE : (a1BaseChangeIso R E V).hom.left ≫
        ((projection T).app ((toSmoothSite E).obj V)).left =
      pullback.fst V.hom (πE).left :=
      pullbackRightPullbackFstIso_hom_fst _ _ _
    have hU : (a1BaseChangeIso R U ((baseChange j.left).obj V)).hom.left ≫
        ((projection T).app ((toSmoothSite U).obj ((baseChange j.left).obj V))).left =
      pullback.fst ((baseChange j.left).obj V).hom (πU).left :=
      pullbackRightPullbackFstIso_hom_fst _ _ _
    have hR : (affineLineCylinder.map ((restrictionProjection j).app V)).left ≫
        ((projection T).app ((toSmoothSite E).obj V)).left =
      ((projection T).app ((toSmoothSite U).obj ((baseChange j.left).obj V))).left ≫
        ((restrictionProjection j).app V).left :=
      congrArg (fun f ↦ f.left) ((projection T).naturality ((restrictionProjection j).app V))
    apply MorphismProperty.Over.Hom.ext
    change (pullback.fst ((baseChange (πE).left).obj V).hom
        (j₁).left ≫ (a1BaseChangeIso R E V).hom.left) ≫
        ((projection T).app ((toSmoothSite E).obj V)).left =
      (((a1PunctureProjectionBaseChangeIso j).hom.app V).left ≫
        (a1BaseChangeIso R U ((baseChange j.left).obj V)).hom.left ≫
        (affineLineCylinder.map ((restrictionProjection j).app V)).left) ≫
        ((projection T).app ((toSmoothSite E).obj V)).left
    simp only [Category.assoc]
    rw [hE, hR, ← Category.assoc (a1BaseChangeIso R U ((baseChange j.left).obj V)).hom.left,
      hU]
    exact (a1PunctureProjectionBaseChangeIso_fst j V).symm
  · have hE : (a1BaseChangeIso R E V).hom.left ≫
        (SmoothSite.productSnd ((toSmoothSite E).obj V) T).left =
      pullback.snd V.hom (πE).left ≫
        (SmoothSite.productSnd E T).left :=
      pullbackRightPullbackFstIso_hom_snd _ _ _
    have hU : (a1BaseChangeIso R U ((baseChange j.left).obj V)).hom.left ≫
        (SmoothSite.productSnd ((toSmoothSite U).obj ((baseChange j.left).obj V))
          T).left =
      pullback.snd ((baseChange j.left).obj V).hom (πU).left ≫
        (SmoothSite.productSnd U T).left :=
      pullbackRightPullbackFstIso_hom_snd _ _ _
    have hR : (affineLineCylinder.map ((restrictionProjection j).app V)).left ≫
        (SmoothSite.productSnd ((toSmoothSite E).obj V) T).left =
      (SmoothSite.productSnd ((toSmoothSite U).obj ((baseChange j.left).obj V))
        T).left := by
      simpa only [affineLineCylinder, parameterProduct, Functor.comp_obj,
        MorphismProperty.Comma.comp_left, Category.comp_id] using
        congrArg (fun f ↦ f.left)
          (SmoothSite.productMap_snd ((restrictionProjection j).app V)
            (𝟙 T))
    have hJ : (j₁).left ≫
        (SmoothSite.productSnd E T).left =
      (SmoothSite.productSnd U T).left := by
      simpa only [affineLineCylinder, parameterProduct, Functor.comp_obj,
        MorphismProperty.Comma.comp_left, Category.comp_id] using
        congrArg (fun f ↦ f.left)
          (SmoothSite.productMap_snd j (𝟙 T))
    have hμ : ((a1PunctureProjectionBaseChangeIso j).hom.app V).left ≫
        pullback.snd ((baseChange j.left).obj V).hom (πU).left =
      pullback.snd ((baseChange (πE).left).obj V).hom
        (j₁).left :=
      MorphismProperty.Over.w ((a1PunctureProjectionBaseChangeIso j).hom.app V)
    apply MorphismProperty.Over.Hom.ext
    simp only [MorphismProperty.Comma.comp_left, Category.assoc]
    rw [hR, hU, hE]
    change pullback.fst ((baseChange (πE).left).obj V).hom
        (j₁).left ≫
        ((baseChange (πE).left).obj V).hom ≫
        (SmoothSite.productSnd E T).left =
      ((a1PunctureProjectionBaseChangeIso j).hom.app V).left ≫
        pullback.snd ((baseChange j.left).obj V).hom (πU).left ≫
        (SmoothSite.productSnd U T).left
    rw [← Category.assoc, pullback.condition, Category.assoc, hJ,
      ← Category.assoc, hμ]

end Product

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
