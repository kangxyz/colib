/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Limits.Pullback.FactorExchange
public import Colib.AlgebraicGeometry.Correspondences.Exterior.MixedCoefficientChart

/-!
# The literal mixed coefficient product becomes a graph product

For an arbitrary native ideal sheaf `W` on `X × Y` and parameter map `ψ : T ⟶ U`,
the coefficient scheme `(X × T) × (W × U)` is reordered to
`(W × T) × (X × U)`. The latter uses the exact structural map of the graph of
`(p,ψ) : W × T → X × U`. Swapping only the two `X` coordinates of the middle
self-product fixes its diagonal and converts the mixed pair to that graph pair.

Every statement is over an arbitrary base scheme. The support and parameter
map are not required to be flat, reduced, integral or connected. These are
actual morphism identities; no Tor or common-regular-list provider is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

@[reassoc]
private theorem mixed_congrHom_fst {C : Type*} [Category C] {A B S : C}
    {f₁ f₂ : A ⟶ S} {g₁ g₂ : B ⟶ S} [HasPullback f₁ g₁] [HasPullback f₂ g₂]
    (hf : f₁ = f₂) (hg : g₁ = g₂) :
    (pullback.congrHom hf hg).hom ≫ pullback.fst f₂ g₂ = pullback.fst f₁ g₁ :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
private theorem mixed_congrHom_snd {C : Type*} [Category C] {A B S : C}
    {f₁ f₂ : A ⟶ S} {g₁ g₂ : B ⟶ S} [HasPullback f₁ g₁] [HasPullback f₂ g₂]
    (hf : f₁ = f₂) (hg : g₁ = g₂) :
    (pullback.congrHom hf hg).hom ≫ pullback.snd f₂ g₂ = pullback.snd f₁ g₁ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

variable {S : Scheme.{u}} (X Y T U : SmoothSite S)
  (W : (pullback X.hom Y.hom).IdealSheafData) (ψ : T ⟶ U)

/-- The actual map `(p,ψ) : W × T → X × U` whose graph will replace the mixed pair. -/
def nativeMixedSupportMap : exteriorIdentitySupport X Y T W ⟶ (SmoothSite.product X U).left :=
  exteriorParameterMap X Y W ψ ≫ exteriorIdentitySource X Y U W

@[reassoc]
theorem nativeMixedSupportMap_eq : nativeMixedSupportMap X Y T U W ψ =
    exteriorIdentitySource X Y T W ≫ (SmoothSite.productMap (𝟙 X) ψ).left :=
  exteriorParameterMap_source X Y W ψ

@[reassoc (attr := simp)]
theorem nativeMixedSupportMap_fst : nativeMixedSupportMap X Y T U W ψ ≫
    pullback.fst X.hom U.hom =
    pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom ≫
      exteriorSupportSourceProjection X Y W := by
  simp only [nativeMixedSupportMap, Category.assoc, exteriorIdentitySource_fst,
    exteriorParameterMap_fst_assoc]

@[reassoc (attr := simp)]
theorem nativeMixedSupportMap_snd : nativeMixedSupportMap X Y T U W ψ ≫
    pullback.snd X.hom U.hom =
    pullback.snd (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom ≫ ψ.left := by
  simp only [nativeMixedSupportMap, Category.assoc, exteriorIdentitySource_snd,
    exteriorParameterMap_snd]

/-- The graph uses the ordinary structural map of the actual support times `T`. -/
@[reassoc]
theorem nativeMixedSupportMap_over : nativeMixedSupportMap X Y T U W ψ ≫
    (SmoothSite.product X U).hom =
    pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom ≫
      (exteriorSupportSourceProjection X Y W ≫ X.hom) := by
  simp only [SmoothSite.product_hom, ← Category.assoc, nativeMixedSupportMap_fst]

/-- Normalize only the displayed structural map, without changing either coefficient factor. -/
def nativeMixedCoefficientFourfoldIso : nativeMixedCoefficient X Y T U W ≅
    pullback.fourfold X.hom T.hom (exteriorSupportSourceProjection X Y W ≫ X.hom) U.hom :=
  pullback.congrHom rfl (by
    simp only [SmoothSite.product_hom, ← Category.assoc, exteriorIdentitySource_fst])

/-- The actual graph ambient product, with the structural map dictated by its source map. -/
abbrev nativeMixedGraphProduct : Scheme.{u} :=
  pullback (nativeMixedSupportMap X Y T U W ψ ≫ (SmoothSite.product X U).hom)
    (SmoothSite.product X U).hom

/-- The middle pair of the actual source-first graph ambient product. -/
def nativeMixedGraphPair : nativeMixedGraphProduct X Y T U W ψ ⟶
    pullback (SmoothSite.product X U).hom (SmoothSite.product X U).hom :=
  pullback.map _ _ _ _ (nativeMixedSupportMap X Y T U W ψ)
    (𝟙 (SmoothSite.product X U).left) (𝟙 S) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem nativeMixedGraphPair_fst : nativeMixedGraphPair X Y T U W ψ ≫
    pullback.fst (pullback.fst X.hom U.hom ≫ X.hom)
      (pullback.fst X.hom U.hom ≫ X.hom) =
    pullback.fst _ _ ≫ nativeMixedSupportMap X Y T U W ψ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem nativeMixedGraphPair_snd : nativeMixedGraphPair X Y T U W ψ ≫
    pullback.snd (pullback.fst X.hom U.hom ≫ X.hom)
      (pullback.fst X.hom U.hom ≫ X.hom) =
    pullback.snd _ _ := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- Reorder the literal coefficient factors and retain the exact graph structural map. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Graph/ProductTransversality.lean:183-205"
  "adaptation" "Native literal coefficient product and exact graph ambient product; no \
    support-flatness hypothesis"]
def nativeMixedCoefficientGraphIso : nativeMixedCoefficient X Y T U W ≅
    nativeMixedGraphProduct X Y T U W ψ :=
  nativeMixedCoefficientFourfoldIso X Y T U W ≪≫
    pullback.fourfoldSwapIso X.hom T.hom (exteriorSupportSourceProjection X Y W ≫ X.hom)
      U.hom ≪≫
    pullback.congrHom (nativeMixedSupportMap_over X Y T U W ψ).symm rfl

/-- The reordered first coordinate is the original support coordinate. -/
@[reassoc (attr := simp)]
theorem nativeMixedCoefficientGraphIso_first :
    (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫ pullback.fst
      (nativeMixedSupportMap X Y T U W ψ ≫ (pullback.fst X.hom U.hom ≫ X.hom))
      (pullback.fst X.hom U.hom ≫ X.hom) ≫
      pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom =
    pullback.snd _ _ ≫
      pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom) U.hom := by
  change (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫ pullback.fst
      (nativeMixedSupportMap X Y T U W ψ ≫ (SmoothSite.product X U).hom)
      (SmoothSite.product X U).hom ≫
      pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom = _
  simp only [nativeMixedCoefficientGraphIso, Iso.trans_hom, Category.assoc]
  rw [mixed_congrHom_fst_assoc (nativeMixedSupportMap_over X Y T U W ψ).symm
    (show pullback.fst X.hom U.hom ≫ X.hom = (SmoothSite.product X U).hom from rfl)
    (pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom)]
  change (nativeMixedCoefficientFourfoldIso X Y T U W).hom ≫
    pullback.fourfoldSwap X.hom T.hom (exteriorSupportSourceProjection X Y W ≫ X.hom)
      U.hom ≫
        pullback.fourfoldFirst (exteriorSupportSourceProjection X Y W ≫ X.hom)
          T.hom X.hom U.hom = _
  rw [pullback.fourfoldSwap_first]
  simpa only [nativeMixedCoefficientFourfoldIso, pullback.fourfoldThird] using
    mixed_congrHom_snd_assoc
      (show (SmoothSite.product X T).hom = pullback.fst X.hom T.hom ≫ X.hom from rfl)
      (nativeMixedCoefficient_second_structure X Y U W)
      (pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom) U.hom)

/-- The reordered second coordinate is the original parameter-source coordinate. -/
@[reassoc (attr := simp)]
theorem nativeMixedCoefficientGraphIso_second :
    (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫ pullback.fst
      (nativeMixedSupportMap X Y T U W ψ ≫ (pullback.fst X.hom U.hom ≫ X.hom))
      (pullback.fst X.hom U.hom ≫ X.hom) ≫
      pullback.snd (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom =
    pullback.fst _ _ ≫ pullback.snd X.hom T.hom := by
  change (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫ pullback.fst
      (nativeMixedSupportMap X Y T U W ψ ≫ (SmoothSite.product X U).hom)
      (SmoothSite.product X U).hom ≫
      pullback.snd (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom = _
  simp only [nativeMixedCoefficientGraphIso, Iso.trans_hom, Category.assoc]
  rw [mixed_congrHom_fst_assoc (nativeMixedSupportMap_over X Y T U W ψ).symm
    (show pullback.fst X.hom U.hom ≫ X.hom = (SmoothSite.product X U).hom from rfl)
    (pullback.snd (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom)]
  change (nativeMixedCoefficientFourfoldIso X Y T U W).hom ≫
    pullback.fourfoldSwap X.hom T.hom (exteriorSupportSourceProjection X Y W ≫ X.hom)
      U.hom ≫
        pullback.fourfoldSecond (exteriorSupportSourceProjection X Y W ≫ X.hom)
          T.hom X.hom U.hom = _
  rw [pullback.fourfoldSwap_second]
  simpa only [nativeMixedCoefficientFourfoldIso, pullback.fourfoldSecond] using
    mixed_congrHom_fst_assoc
      (show (SmoothSite.product X T).hom = pullback.fst X.hom T.hom ≫ X.hom from rfl)
      (nativeMixedCoefficient_second_structure X Y U W)
      (pullback.snd X.hom T.hom)

/-- The reordered third coordinate is the original `X` coordinate. -/
@[reassoc (attr := simp)]
theorem nativeMixedCoefficientGraphIso_third :
    (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫ pullback.snd
      (nativeMixedSupportMap X Y T U W ψ ≫ (pullback.fst X.hom U.hom ≫ X.hom))
      (pullback.fst X.hom U.hom ≫ X.hom) ≫
      pullback.fst X.hom U.hom =
    pullback.fst _ _ ≫ pullback.fst X.hom T.hom := by
  change (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫ pullback.snd
      (nativeMixedSupportMap X Y T U W ψ ≫ (SmoothSite.product X U).hom)
      (SmoothSite.product X U).hom ≫
      pullback.fst X.hom U.hom = _
  simp only [nativeMixedCoefficientGraphIso, Iso.trans_hom, Category.assoc]
  rw [mixed_congrHom_snd_assoc (nativeMixedSupportMap_over X Y T U W ψ).symm
    (show pullback.fst X.hom U.hom ≫ X.hom = (SmoothSite.product X U).hom from rfl)
    (pullback.fst X.hom U.hom)]
  change (nativeMixedCoefficientFourfoldIso X Y T U W).hom ≫
    pullback.fourfoldSwap X.hom T.hom (exteriorSupportSourceProjection X Y W ≫ X.hom)
      U.hom ≫
        pullback.fourfoldThird (exteriorSupportSourceProjection X Y W ≫ X.hom)
          T.hom X.hom U.hom = _
  rw [pullback.fourfoldSwap_third]
  simpa only [nativeMixedCoefficientFourfoldIso, pullback.fourfoldFirst] using
    mixed_congrHom_fst_assoc
      (show (SmoothSite.product X T).hom = pullback.fst X.hom T.hom ≫ X.hom from rfl)
      (nativeMixedCoefficient_second_structure X Y U W)
      (pullback.fst X.hom T.hom)

/-- The reordered fourth coordinate is the original parameter-target coordinate. -/
@[reassoc (attr := simp)]
theorem nativeMixedCoefficientGraphIso_fourth :
    (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫ pullback.snd
      (nativeMixedSupportMap X Y T U W ψ ≫ (pullback.fst X.hom U.hom ≫ X.hom))
      (pullback.fst X.hom U.hom ≫ X.hom) ≫
      pullback.snd X.hom U.hom =
    pullback.snd _ _ ≫
      pullback.snd (exteriorSupportSourceProjection X Y W ≫ X.hom) U.hom := by
  change (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫ pullback.snd
      (nativeMixedSupportMap X Y T U W ψ ≫ (SmoothSite.product X U).hom)
      (SmoothSite.product X U).hom ≫
      pullback.snd X.hom U.hom = _
  simp only [nativeMixedCoefficientGraphIso, Iso.trans_hom, Category.assoc]
  rw [mixed_congrHom_snd_assoc (nativeMixedSupportMap_over X Y T U W ψ).symm
    (show pullback.fst X.hom U.hom ≫ X.hom = (SmoothSite.product X U).hom from rfl)
    (pullback.snd X.hom U.hom)]
  change (nativeMixedCoefficientFourfoldIso X Y T U W).hom ≫
    pullback.fourfoldSwap X.hom T.hom (exteriorSupportSourceProjection X Y W ≫ X.hom)
      U.hom ≫
        pullback.fourfoldFourth (exteriorSupportSourceProjection X Y W ≫ X.hom)
          T.hom X.hom U.hom = _
  rw [pullback.fourfoldSwap_fourth]
  simpa only [nativeMixedCoefficientFourfoldIso, pullback.fourfoldFourth] using
    mixed_congrHom_snd_assoc
      (show (SmoothSite.product X T).hom = pullback.fst X.hom T.hom ≫ X.hom from rfl)
      (nativeMixedCoefficient_second_structure X Y U W)
      (pullback.snd (exteriorSupportSourceProjection X Y W ≫ X.hom) U.hom)

/-- Swap the two `X` coordinates of the middle self-product, retaining both `U` coordinates. -/
def nativeMixedMiddleSwap :
    pullback (SmoothSite.product X U).hom (SmoothSite.product X U).hom ≅
      pullback (SmoothSite.product X U).hom (SmoothSite.product X U).hom :=
  pullback.fourfoldSwapIso X.hom U.hom X.hom U.hom

/-- The middle automorphism fixes the actual diagonal as a scheme morphism. -/
@[reassoc (attr := simp), colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Graph/ProductTransversality.lean:244-257"
  "adaptation" "Partial middle-factor exchange fixes the actual product diagonal"]
theorem diagonal_nativeMixedMiddleSwap :
    pullback.diagonal (pullback.fst X.hom U.hom ≫ X.hom) ≫ (nativeMixedMiddleSwap X U).hom =
      pullback.diagonal (SmoothSite.product X U).hom :=
  pullback.diagonal_fourfoldSwap X.hom U.hom

private theorem productMap_id_fst :
    (SmoothSite.productMap (𝟙 X) ψ).left ≫ pullback.fst X.hom U.hom =
      pullback.fst X.hom T.hom := by
  change (SmoothSite.productMap (𝟙 X) ψ ≫ SmoothSite.productFst X U).left = _
  rw [SmoothSite.productMap_fst, Category.comp_id]
  rfl

private theorem productMap_id_snd :
    (SmoothSite.productMap (𝟙 X) ψ).left ≫ pullback.snd X.hom U.hom =
      pullback.snd X.hom T.hom ≫ ψ.left := by
  change (SmoothSite.productMap (𝟙 X) ψ ≫ SmoothSite.productSnd X U).left = _
  rw [SmoothSite.productMap_snd]
  rfl

/-- The first mixed middle coordinate is the original `X` coordinate. -/
@[reassoc]
theorem nativeMixedCoefficientPair_first : nativeMixedCoefficientPair X Y T U W ψ ≫
    pullback.fourfoldFirst X.hom U.hom X.hom U.hom =
    pullback.fst _ _ ≫ pullback.fst X.hom T.hom := by
  simpa only [pullback.fourfoldFirst, SmoothSite.product_hom, productMap_id_fst] using
    nativeMixedCoefficientPair_fst_assoc X Y T U W ψ (pullback.fst X.hom U.hom)

/-- The second mixed middle coordinate is the image of the source parameter. -/
@[reassoc]
theorem nativeMixedCoefficientPair_second : nativeMixedCoefficientPair X Y T U W ψ ≫
    pullback.fourfoldSecond X.hom U.hom X.hom U.hom =
    pullback.fst _ _ ≫ pullback.snd X.hom T.hom ≫ ψ.left := by
  simpa only [pullback.fourfoldSecond, SmoothSite.product_hom, productMap_id_snd] using
    nativeMixedCoefficientPair_fst_assoc X Y T U W ψ (pullback.snd X.hom U.hom)

/-- The third mixed middle coordinate is the actual support source coordinate. -/
@[reassoc]
theorem nativeMixedCoefficientPair_third : nativeMixedCoefficientPair X Y T U W ψ ≫
    pullback.fourfoldThird X.hom U.hom X.hom U.hom =
    pullback.snd _ _ ≫ pullback.fst
      (exteriorSupportSourceProjection X Y W ≫ X.hom) U.hom ≫
        exteriorSupportSourceProjection X Y W := by
  simpa only [pullback.fourfoldThird, SmoothSite.product_hom, exteriorIdentitySource_fst] using
    nativeMixedCoefficientPair_snd_assoc X Y T U W ψ (pullback.fst X.hom U.hom)

/-- The fourth mixed middle coordinate is the target parameter. -/
@[reassoc]
theorem nativeMixedCoefficientPair_fourth : nativeMixedCoefficientPair X Y T U W ψ ≫
    pullback.fourfoldFourth X.hom U.hom X.hom U.hom =
    pullback.snd _ _ ≫
      pullback.snd (exteriorSupportSourceProjection X Y W ≫ X.hom) U.hom := by
  simpa only [pullback.fourfoldFourth, SmoothSite.product_hom, exteriorIdentitySource_snd] using
    nativeMixedCoefficientPair_snd_assoc X Y T U W ψ (pullback.snd X.hom U.hom)

/-- After exchanging the coefficient factors, the mixed pair becomes the ordinary graph pair
under the diagonal-fixing middle automorphism. -/
@[reassoc, colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Graph/ProductTransversality.lean:259-280"
  "adaptation" "Literal native mixed-pair/graph-pair equality under coefficient and \
    middle factor exchange"]
theorem nativeMixedCoefficientPair_exchange :
    nativeMixedCoefficientPair X Y T U W ψ ≫ (nativeMixedMiddleSwap X U).hom =
      (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫ nativeMixedGraphPair X Y T U W ψ := by
  apply pullback.fourfold_hom_ext
  · simp only [Category.assoc, nativeMixedMiddleSwap, pullback.fourfoldSwapIso,
      pullback.fourfoldSwap_first, nativeMixedCoefficientPair_third]
    change _ = (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫
      nativeMixedGraphPair X Y T U W ψ ≫
        pullback.fst (SmoothSite.product X U).hom (SmoothSite.product X U).hom ≫
          pullback.fst X.hom U.hom
    have pairProjection := nativeMixedGraphPair_fst_assoc X Y T U W ψ (pullback.fst X.hom U.hom)
    change nativeMixedGraphPair X Y T U W ψ ≫
      pullback.fst (SmoothSite.product X U).hom (SmoothSite.product X U).hom ≫
        pullback.fst X.hom U.hom = _ at pairProjection
    have isoProjection := nativeMixedCoefficientGraphIso_first_assoc X Y T U W ψ
      (exteriorSupportSourceProjection X Y W)
    change (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫
      pullback.fst (nativeMixedSupportMap X Y T U W ψ ≫ (SmoothSite.product X U).hom)
        (SmoothSite.product X U).hom ≫
          pullback.fst (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom ≫
            exteriorSupportSourceProjection X Y W = _ at isoProjection
    simp only [pairProjection, nativeMixedSupportMap_fst,
      isoProjection]
  · simp only [Category.assoc, nativeMixedMiddleSwap, pullback.fourfoldSwapIso,
      pullback.fourfoldSwap_second, nativeMixedCoefficientPair_second]
    change _ = (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫
      nativeMixedGraphPair X Y T U W ψ ≫
        pullback.fst (SmoothSite.product X U).hom (SmoothSite.product X U).hom ≫
          pullback.snd X.hom U.hom
    have pairProjection := nativeMixedGraphPair_fst_assoc X Y T U W ψ (pullback.snd X.hom U.hom)
    change nativeMixedGraphPair X Y T U W ψ ≫
      pullback.fst (SmoothSite.product X U).hom (SmoothSite.product X U).hom ≫
        pullback.snd X.hom U.hom = _ at pairProjection
    have isoProjection := nativeMixedCoefficientGraphIso_second_assoc X Y T U W ψ (ψ.left)
    change (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫
      pullback.fst (nativeMixedSupportMap X Y T U W ψ ≫ (SmoothSite.product X U).hom)
        (SmoothSite.product X U).hom ≫
          pullback.snd (exteriorSupportSourceProjection X Y W ≫ X.hom) T.hom ≫
            ψ.left = _ at isoProjection
    simp only [pairProjection, nativeMixedSupportMap_snd,
      isoProjection]
  · simp only [Category.assoc, nativeMixedMiddleSwap, pullback.fourfoldSwapIso,
      pullback.fourfoldSwap_third, nativeMixedCoefficientPair_first]
    change _ = (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫
      nativeMixedGraphPair X Y T U W ψ ≫
        pullback.snd (SmoothSite.product X U).hom (SmoothSite.product X U).hom ≫
          pullback.fst X.hom U.hom
    have pairProjection := nativeMixedGraphPair_snd_assoc X Y T U W ψ (pullback.fst X.hom U.hom)
    change nativeMixedGraphPair X Y T U W ψ ≫
      pullback.snd (SmoothSite.product X U).hom (SmoothSite.product X U).hom ≫
        pullback.fst X.hom U.hom = _ at pairProjection
    have isoProjection := nativeMixedCoefficientGraphIso_third X Y T U W ψ
    change (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫
      pullback.snd (nativeMixedSupportMap X Y T U W ψ ≫ (SmoothSite.product X U).hom)
        (SmoothSite.product X U).hom ≫
          pullback.fst X.hom U.hom = _ at isoProjection
    simp only [pairProjection, isoProjection]
  · simp only [Category.assoc, nativeMixedMiddleSwap, pullback.fourfoldSwapIso,
      pullback.fourfoldSwap_fourth, nativeMixedCoefficientPair_fourth]
    change _ = (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫
      nativeMixedGraphPair X Y T U W ψ ≫
        pullback.snd (SmoothSite.product X U).hom (SmoothSite.product X U).hom ≫
          pullback.snd X.hom U.hom
    have pairProjection := nativeMixedGraphPair_snd_assoc X Y T U W ψ (pullback.snd X.hom U.hom)
    change nativeMixedGraphPair X Y T U W ψ ≫
      pullback.snd (SmoothSite.product X U).hom (SmoothSite.product X U).hom ≫
        pullback.snd X.hom U.hom = _ at pairProjection
    have isoProjection := nativeMixedCoefficientGraphIso_fourth X Y T U W ψ
    change (nativeMixedCoefficientGraphIso X Y T U W ψ).hom ≫
      pullback.snd (nativeMixedSupportMap X Y T U W ψ ≫ (SmoothSite.product X U).hom)
        (SmoothSite.product X U).hom ≫
          pullback.snd X.hom U.hom = _ at isoProjection
    simp only [pairProjection, isoProjection]

/-- In reverse, the ordinary graph pair becomes the literal mixed pair. -/
@[reassoc]
theorem nativeMixedGraphPair_exchange :
    nativeMixedGraphPair X Y T U W ψ ≫ (nativeMixedMiddleSwap X U).hom =
      (nativeMixedCoefficientGraphIso X Y T U W ψ).inv ≫
        nativeMixedCoefficientPair X Y T U W ψ := by
  apply (cancel_epi (nativeMixedCoefficientGraphIso X Y T U W ψ).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← nativeMixedCoefficientPair_exchange, Category.assoc]
  simp only [nativeMixedMiddleSwap, pullback.fourfoldSwapIso, pullback.fourfoldSwap_comp]
  exact Category.comp_id _

/-- The actual source-first graph of `(p,ψ)`, using the existing native graph map. -/
abbrev nativeMixedGraphEmbedding : exteriorIdentitySupport X Y T W ⟶
    nativeMixedGraphProduct X Y T U W ψ :=
  correspondenceGraphMap
    (nativeMixedSupportMap X Y T U W ψ ≫ (SmoothSite.product X U).hom)
    (SmoothSite.product X U).hom (nativeMixedSupportMap X Y T U W ψ) rfl

/-- The actual graph maps to the middle diagonal under its graph pair. -/
@[reassoc]
theorem nativeMixedGraphEmbedding_pair :
    nativeMixedGraphEmbedding X Y T U W ψ ≫ nativeMixedGraphPair X Y T U W ψ =
      nativeMixedSupportMap X Y T U W ψ ≫ pullback.diagonal (SmoothSite.product X U).hom := by
  have pairFst := nativeMixedGraphPair_fst X Y T U W ψ
  change nativeMixedGraphPair X Y T U W ψ ≫
    pullback.fst (SmoothSite.product X U).hom (SmoothSite.product X U).hom = _ at pairFst
  have pairSnd := nativeMixedGraphPair_snd X Y T U W ψ
  change nativeMixedGraphPair X Y T U W ψ ≫
    pullback.snd (SmoothSite.product X U).hom (SmoothSite.product X U).hom = _ at pairSnd
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pairFst, pairSnd,
      nativeMixedGraphEmbedding, correspondenceGraphMap_fst_assoc,
      correspondenceGraphMap_snd, pullback.diagonal_fst, pullback.diagonal_snd,
      Category.comp_id]

/-- The actual graph, returned to the original coefficient factor order. -/
def nativeMixedCoefficientEmbedding : exteriorIdentitySupport X Y T W ⟶
    nativeMixedCoefficient X Y T U W :=
  nativeMixedGraphEmbedding X Y T U W ψ ≫ (nativeMixedCoefficientGraphIso X Y T U W ψ).inv

/-- The transported graph has exactly the original middle diagonal as its mixed pair. -/
@[reassoc, colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Graph/ProductTransversality.lean:282-290"
  "adaptation" "Actual graph embedding transported back to the literal mixed coefficient scheme"]
theorem nativeMixedCoefficientEmbedding_pair :
    nativeMixedCoefficientEmbedding X Y T U W ψ ≫
      nativeMixedCoefficientPair X Y T U W ψ =
    nativeMixedSupportMap X Y T U W ψ ≫ pullback.diagonal (SmoothSite.product X U).hom := by
  have diagonalSwap := diagonal_nativeMixedMiddleSwap X U
  change pullback.diagonal (SmoothSite.product X U).hom ≫ (nativeMixedMiddleSwap X U).hom =
    _ at diagonalSwap
  rw [nativeMixedCoefficientEmbedding, Category.assoc, ← nativeMixedGraphPair_exchange,
    ← Category.assoc, nativeMixedGraphEmbedding_pair, Category.assoc,
    diagonalSwap]

end Stacks.Chow
