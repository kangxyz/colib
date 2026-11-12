/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ParameterProduct
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ImageAdjunction
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Continuity

/-!
# Restriction of parameter sections to the small Nisnevich site

The small-site direct image is computed by literal base change of the
étale neighborhoods. The identification retains the original smooth
parameter product and every neighborhood morphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {B : Scheme.{u}} (X T : SmoothSite B)

local notation "XT" => SmoothSite.product X T
set_option quotPrecheck false in
local notation "π" => (SmoothSite.productFst X T).left

/-- The actual base change along the parameter projection is the literal
neighborhood product. -/
def baseChangeParameterProductIso : baseChange π ≅ parameterProduct X T :=
  NatIso.ofComponents (fun V =>
    MorphismProperty.Over.isoMk (parameterProduct_isPullback X T V).flip.isoPullback.symm
      (parameterProduct_isPullback X T V).flip.isoPullback_inv_snd)
    (fun {V W} a => by
      apply MorphismProperty.Over.Hom.ext
      let eV := (parameterProduct_isPullback X T V).flip.isoPullback
      let eW := (parameterProduct_isPullback X T W).flip.isoPullback
      change ((baseChange π).map a).left ≫ eW.inv =
        eV.inv ≫ ((parameterProduct X T).map a).left
      apply (cancel_mono eW.hom).mp
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc]
      apply pullback.hom_ext (f := W.hom) (g := π)
      · have hMap : ((baseChange π).map a).left ≫ pullback.fst W.hom π =
            pullback.fst V.hom π ≫ a.left := pullback.lift_fst _ _ _
        have hW : eW.hom ≫ pullback.fst W.hom π =
            (SmoothSite.productFst ((toSmoothSite X).obj W) T).left :=
          (parameterProduct_isPullback X T W).flip.isoPullback_hom_fst
        have hV : eV.inv ≫ (SmoothSite.productFst ((toSmoothSite X).obj V) T).left =
            pullback.fst V.hom π := (parameterProduct_isPullback X T V).flip.isoPullback_inv_fst
        have h := congrArg (fun f => f.left)
          (SmoothSite.productMap_fst ((toSmoothSite X).map a) (𝟙 T))
        change ((parameterProduct X T).map a).left ≫
            (SmoothSite.productFst ((toSmoothSite X).obj W) T).left =
          (SmoothSite.productFst ((toSmoothSite X).obj V) T).left ≫ a.left at h
        change ((baseChange π).map a).left ≫ pullback.fst W.hom π =
          eV.inv ≫ (((parameterProduct X T).map a).left ≫ eW.hom ≫ pullback.fst W.hom π)
        have hV' : eV.inv ≫ (((toSmoothSite X).obj V).productFst T).left ≫ a.left =
            pullback.fst V.hom π ≫ a.left :=
          (Category.assoc _ _ _).symm.trans (congrArg (· ≫ a.left) hV)
        exact hMap.trans (hV'.symm.trans (congrArg (eV.inv ≫ ·) (h.symm.trans
          (congrArg (((parameterProduct X T).map a).left ≫ ·) hW.symm))))
      · have hW : eW.hom ≫ pullback.snd W.hom π = ((parameterProduct X T).obj W).hom :=
          (parameterProduct_isPullback X T W).flip.isoPullback_hom_snd
        have hV : eV.inv ≫ ((parameterProduct X T).obj V).hom = pullback.snd V.hom π :=
          (parameterProduct_isPullback X T V).flip.isoPullback_inv_snd
        have hMap : ((baseChange π).map a).left ≫ pullback.snd W.hom π =
            pullback.snd V.hom π := MorphismProperty.Over.w ((baseChange π).map a)
        change ((baseChange π).map a).left ≫ pullback.snd W.hom π =
          eV.inv ≫ (((parameterProduct X T).map a).left ≫ eW.hom ≫ pullback.snd W.hom π)
        exact hMap.trans (hV.symm.trans (congrArg (eV.inv ≫ ·)
          ((MorphismProperty.Over.w ((parameterProduct X T).map a)).symm.trans
            (congrArg (((parameterProduct X T).map a).left ≫ ·) hW.symm)))))

/-- On the smooth site, the actual base-changed neighborhoods are the
original neighborhoods multiplied by the parameter. -/
def baseChangeParameterProductUnderlyingIso :
    baseChange π ⋙ toSmoothSite XT ≅
      toSmoothSite X ⋙ SmoothSite.Contraction.parameterProduct T :=
  Functor.isoWhiskerRight (baseChangeParameterProductIso X T) _ ≪≫
    parameterProductUnderlyingIso X T

/-- Smooth parameter reindexing, restricted to the small site, is the
actual direct image of the restricted coefficients on the parameter product. -/
def restrictParameterSectionsIso :
    (SmoothSite.Contraction.parameterProduct T).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (SmoothSite.nisnevichTopology B) (SmoothSite.nisnevichTopology B) ⋙
      restrict X AddCommGrpCat.{u + 1} ≅
    restrict XT AddCommGrpCat.{u + 1} ⋙ directImage π := by
  let A := AddCommGrpCat.{u + 1}
  let J := SmoothSite.nisnevichTopology B
  let J₀ := nisnevichTopology X.left
  let J₁ := nisnevichTopology (XT).left
  let F := toSmoothSite X
  let G := SmoothSite.Contraction.parameterProduct T
  let F' := baseChange π
  let G' := toSmoothSite XT
  let : (F ⋙ G).IsContinuous J₀ J := Functor.isContinuous_comp F G J₀ J J
  let : (F' ⋙ G').IsContinuous J₀ J := Functor.isContinuous_comp F' G' J₀ J₁ J
  exact Functor.sheafPushforwardContinuousIso
    (baseChangeParameterProductUnderlyingIso X T).symm A J₀ J

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
