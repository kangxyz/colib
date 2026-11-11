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
`Motivic/Cohomology/A1/Boundary/Contraction/ProjectionExcisionGeometry.lean`, blob `658ae71e7f064cc3716386a67a91d0d7e1366604`.
Only the original Product section is extracted. No normal-chart product,
support comparison or canonical boundary epimorphism is used.
Source candidate only; no elaboration result is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

section Product

variable {R : CommRingCat.{u}} {U E : SmoothSite (Spec R)} (j : U ⟶ E)

/-- The literal product square of a puncture commutes on actual neighborhood
pullbacks, without any coefficient inverse-image comparison. -/
def a1PunctureProjectionBaseChangeIso :
    baseChange ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app E).left ⋙
        baseChange (SmoothSite.Contraction.affineLineCylinder.map j).left ≅
      baseChange j.left ⋙ baseChange ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app U).left :=
  (MorphismProperty.Over.pullbackComp (P := etaleSeparatedFiniteType) (Q := ⊤)
    (SmoothSite.Contraction.affineLineCylinder.map j).left ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app E).left).symm ≪≫
    MorphismProperty.Over.pullbackComp ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app U).left j.left
      (fg := (SmoothSite.Contraction.affineLineCylinder.map j ≫ (SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app E).left)
      (hfg := congrArg (fun f ↦ f.left) ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).naturality j))

/-- The product-puncture comparison retains the original ambient projection. -/
@[reassoc (attr := simp)]
theorem a1PunctureProjectionBaseChangeIso_fst (V : EtaleSeparatedFiniteType E.left) :
    ((a1PunctureProjectionBaseChangeIso j).hom.app V).left ≫
        pullback.fst (pullback.snd V.hom j.left)
          (pullback.fst U.hom ((SmoothSite.additiveGroupObject (Spec R)).hom)) ≫
        pullback.fst V.hom j.left =
      pullback.fst (pullback.snd V.hom ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app E).left)
          (SmoothSite.Contraction.affineLineCylinder.map j).left ≫
        pullback.fst V.hom ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app E).left := by
  simp [a1PunctureProjectionBaseChangeIso,
    MorphismProperty.Over.pullbackComp_hom_app_left,
    MorphismProperty.Over.pullbackComp_inv_app_left]

/-- The actual puncture restriction commutes with the original base-change to
cylinder comparison. This is an equality of the specified geometric maps, not
an identification of coefficient inverse images. -/
theorem a1PunctureProjectionBaseChangeIso_restriction (V : EtaleSeparatedFiniteType E.left) :
    (restrictionProjection (SmoothSite.Contraction.affineLineCylinder.map j)).app
        ((baseChange ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app E).left).obj V) ≫
        (a1BaseChangeIso R E V).hom =
      (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj U)).map
          ((a1PunctureProjectionBaseChangeIso j).hom.app V) ≫
        (a1BaseChangeIso R U ((baseChange j.left).obj V)).hom ≫
        SmoothSite.Contraction.affineLineCylinder.map ((restrictionProjection j).app V) := by
  apply SmoothSite.product_hom_ext
  · have hE : (a1BaseChangeIso R E V).hom.left ≫
        ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app ((toSmoothSite E).obj V)).left =
      pullback.fst V.hom ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app E).left :=
      pullbackRightPullbackFstIso_hom_fst _ _ _
    have hU : (a1BaseChangeIso R U ((baseChange j.left).obj V)).hom.left ≫
        ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app ((toSmoothSite U).obj ((baseChange j.left).obj V))).left =
      pullback.fst ((baseChange j.left).obj V).hom ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app U).left :=
      pullbackRightPullbackFstIso_hom_fst _ _ _
    have hR : (SmoothSite.Contraction.affineLineCylinder.map ((restrictionProjection j).app V)).left ≫
        ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app ((toSmoothSite E).obj V)).left =
      ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app ((toSmoothSite U).obj ((baseChange j.left).obj V))).left ≫
        ((restrictionProjection j).app V).left :=
      congrArg (fun f ↦ f.left) ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).naturality ((restrictionProjection j).app V))
    apply MorphismProperty.Over.Hom.ext
    change (pullback.fst ((baseChange ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app E).left).obj V).hom
        (SmoothSite.Contraction.affineLineCylinder.map j).left ≫ (a1BaseChangeIso R E V).hom.left) ≫
        ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app ((toSmoothSite E).obj V)).left =
      (((a1PunctureProjectionBaseChangeIso j).hom.app V).left ≫
        (a1BaseChangeIso R U ((baseChange j.left).obj V)).hom.left ≫
        (SmoothSite.Contraction.affineLineCylinder.map ((restrictionProjection j).app V)).left) ≫
        ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app ((toSmoothSite E).obj V)).left
    simp only [Category.assoc]
    rw [hE, hR, ← Category.assoc (a1BaseChangeIso R U ((baseChange j.left).obj V)).hom.left,
      hU]
    exact (a1PunctureProjectionBaseChangeIso_fst j V).symm
  · have hE : (a1BaseChangeIso R E V).hom.left ≫
        (SmoothSite.productSnd ((toSmoothSite E).obj V) (SmoothSite.additiveGroupObject (Spec R))).left =
      pullback.snd V.hom ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app E).left ≫
        (SmoothSite.productSnd E (SmoothSite.additiveGroupObject (Spec R))).left :=
      pullbackRightPullbackFstIso_hom_snd _ _ _
    have hU : (a1BaseChangeIso R U ((baseChange j.left).obj V)).hom.left ≫
        (SmoothSite.productSnd ((toSmoothSite U).obj ((baseChange j.left).obj V))
          (SmoothSite.additiveGroupObject (Spec R))).left =
      pullback.snd ((baseChange j.left).obj V).hom ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app U).left ≫
        (SmoothSite.productSnd U (SmoothSite.additiveGroupObject (Spec R))).left :=
      pullbackRightPullbackFstIso_hom_snd _ _ _
    have hR : (SmoothSite.Contraction.affineLineCylinder.map ((restrictionProjection j).app V)).left ≫
        (SmoothSite.productSnd ((toSmoothSite E).obj V) (SmoothSite.additiveGroupObject (Spec R))).left =
      (SmoothSite.productSnd ((toSmoothSite U).obj ((baseChange j.left).obj V))
        (SmoothSite.additiveGroupObject (Spec R))).left := by
      simpa only [SmoothSite.Contraction.affineLineCylinder, SmoothSite.Contraction.parameterProduct, Functor.comp_obj,
        MorphismProperty.Comma.comp_left, Category.comp_id] using
        congrArg (fun f ↦ f.left)
          (SmoothSite.productMap_snd ((restrictionProjection j).app V)
            (𝟙 (SmoothSite.additiveGroupObject (Spec R))))
    have hJ : (SmoothSite.Contraction.affineLineCylinder.map j).left ≫
        (SmoothSite.productSnd E (SmoothSite.additiveGroupObject (Spec R))).left =
      (SmoothSite.productSnd U (SmoothSite.additiveGroupObject (Spec R))).left := by
      simpa only [SmoothSite.Contraction.affineLineCylinder, SmoothSite.Contraction.parameterProduct, Functor.comp_obj,
        MorphismProperty.Comma.comp_left, Category.comp_id] using
        congrArg (fun f ↦ f.left)
          (SmoothSite.productMap_snd j (𝟙 (SmoothSite.additiveGroupObject (Spec R))))
    have hμ : ((a1PunctureProjectionBaseChangeIso j).hom.app V).left ≫
        pullback.snd ((baseChange j.left).obj V).hom ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app U).left =
      pullback.snd ((baseChange ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app E).left).obj V).hom
        (SmoothSite.Contraction.affineLineCylinder.map j).left :=
      MorphismProperty.Over.w ((a1PunctureProjectionBaseChangeIso j).hom.app V)
    apply MorphismProperty.Over.Hom.ext
    simp only [MorphismProperty.Comma.comp_left, Category.assoc]
    rw [hR, hU, hE]
    change pullback.fst ((baseChange ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app E).left).obj V).hom
        (SmoothSite.Contraction.affineLineCylinder.map j).left ≫
        ((baseChange ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app E).left).obj V).hom ≫
        (SmoothSite.productSnd E (SmoothSite.additiveGroupObject (Spec R))).left =
      ((a1PunctureProjectionBaseChangeIso j).hom.app V).left ≫
        pullback.snd ((baseChange j.left).obj V).hom ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app U).left ≫
        (SmoothSite.productSnd U (SmoothSite.additiveGroupObject (Spec R))).left
    rw [← Category.assoc, pullback.condition, Category.assoc, hJ,
      ← Category.assoc, hμ]

end Product

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
