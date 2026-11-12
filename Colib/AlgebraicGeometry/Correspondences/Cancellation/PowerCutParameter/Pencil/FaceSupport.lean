/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.Pencil.Endpoints
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.Pencil.PolynomialParameter
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.Pencil.Retained
public import Colib.AlgebraicGeometry.Correspondences.Graph.ClosedEndpointSpecialization

/-!
# The closed support of a pencil face

The whole scalar fiber of the retained support is the original support.
Its two projections are the original source base and the original target
with both Laurent coordinates retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction AffineLineFiber

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))} {P : Scheme.{u}}
  (j : P ⟶ pullback
    (product X (multiplicativeGroupObject (Spec (.of k)))).hom
    (product Y (multiplicativeGroupObject (Spec (.of k)))).hom)

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "T" => multiplicativeGroupObject Sₖ
local notation "A₁" => additiveGroupObject Sₖ
local notation "XG" => (product X T)
local notation "YG" => (product Y T)
local notation "V" => (torusPowerCutRetainedTarget k Y)
local notation "B" => (product X A₁)
set_option quotPrecheck false in
local notation "g" => (j ≫ pullback.fst (XG).hom (YG).hom)
set_option quotPrecheck false in
local notation "r" => (j ≫ (torusPowerCutAmbientSchemeIso k X Y).hom)
set_option quotPrecheck false in
local notation "b" => (g ≫ (XG).hom)
local notation "p" => torusPowerCutPencilProjection k g
local notation "p₀" => torusSupportBaseProjection k g
local notation "m" => torusPowerCutPencilRetainedSupportMap k j
local notation "q" => nativeAdditivePolynomialParameter X.hom
local notation "f" => nativeAdditivePolynomialParameter b
local notation "φ(" a ")" => nativeAffineSection (CommRingCat.of k) X a

/-- The actual base map of the retained endpoint support is unchanged. -/
@[reassoc]
theorem torusPowerCutPencilRetainedEndpoint_fst :
    r ≫ pullback.fst X.hom (V).hom = p₀ := by
  have h := congrArg (fun v => v.left) (torusPowerCutAmbientIso_hom_source k X Y)
  change (torusPowerCutAmbientIso k X Y).hom.left ≫ (productFst X V).left =
    (productFst XG YG).left ≫ (productFst X T).left at h
  change (j ≫ (torusPowerCutAmbientIso k X Y).hom.left) ≫ (productFst X V).left = _
  rw [Category.assoc, h]
  exact (Category.assoc _ _ _).symm

/-- The polynomial parameter is the actual second projection of the retained family. -/
theorem torusPowerCutPencilRetainedSupport_parameter :
    m ≫ pullback.fst (B).hom (V).hom ≫ q = f := by
  rw [torusPowerCutPencilRetainedSupportMap_fst_assoc]
  let e : (A₁).left ⟶ Spec (.of (Polynomial k)) := (nativePolynomialAffineLineIso (.of k)).hom
  change (supportParameterExtension g A₁ ≫ (productFst B T).left) ≫
      (productSnd X A₁).left ≫ e = pullback.snd b (A₁).hom ≫ e
  exact (Category.assoc _ _ _).trans (supportParameterExtension_parameter_assoc g A₁ e)

/-- The original smooth-site face is Cartesian for the actual polynomial parameter. -/
theorem torusPowerCutPencilFace_isPullback (X : SmoothSite (Spec (.of k))) (a : k) :
    IsPullback (nativeAffineSection (.of k) X a).left X.hom
      (nativeAdditivePolynomialParameter X.hom) (point a) := by
  rw [← nativeAdditiveParameterSection_eq_nativeAffineSection_left]
  exact nativeAdditiveParameterSection_isPullback X.hom a

/-- The closed-support face map retains the original maps of the entire support. -/
theorem torusPowerCutPencilRetainedSupportMap_endpoint (a : k) :
    (nativeAdditiveParameterFiberIso b a).hom ≫
      closedSupportEndpointMapOfParameterEq (φ(a)) q a
        (torusPowerCutPencilFace_isPullback k X a) m f
        (torusPowerCutPencilRetainedSupport_parameter k j) = r := by
  let v := closedSupportEndpointMapOfParameterEq (φ(a)) q a
    (torusPowerCutPencilFace_isPullback k X a) m f
    (torusPowerCutPencilRetainedSupport_parameter k j)
  let M : pullback X.hom (V).hom ⟶ pullback (B).hom (V).hom :=
    correspondenceGraphFiberAmbientMap X.hom (B).hom (V).hom (φ(a)).left
      (MorphismProperty.Over.w (φ(a)))
  have he : v ≫ M = inclusion f a ≫ m := closedSupportEndpointMapOfParameterEq_ambient (φ(a)) q a
    (torusPowerCutPencilFace_isPullback k X a) m f
    (torusPowerCutPencilRetainedSupport_parameter k j)
  have hproject {E : Scheme.{u}} (s : pullback (B).hom (V).hom ⟶ E) :
      v ≫ M ≫ s = inclusion f a ≫ m ≫ s :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ s) he).trans (Category.assoc _ _ _))
  have hMf : M ≫ pullback.fst (B).hom (V).hom = pullback.fst X.hom (V).hom ≫ (φ(a)).left :=
    pullback.lift_fst _ _ _
  have hMs : M ≫ pullback.snd (B).hom (V).hom = pullback.snd X.hom (V).hom :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hp : v ≫ pullback.fst X.hom (V).hom ≫ (φ(a)).left = inclusion f a ≫ p := by
    exact (congrArg (v ≫ ·) hMf.symm).trans
      ((hproject _).trans
        (congrArg (inclusion f a ≫ ·) (torusPowerCutPencilRetainedSupportMap_fst k j)))
  have ht : v ≫ pullback.snd X.hom (V).hom =
      inclusion f a ≫ pullback.fst b (A₁).hom ≫ r ≫ pullback.snd X.hom (V).hom := by
    exact (congrArg (v ≫ ·) hMs.symm).trans
      ((hproject _).trans
        (congrArg (inclusion f a ≫ ·) (torusPowerCutPencilRetainedSupportMap_snd k j)))
  change (nativeAdditiveParameterFiberIso b a).hom ≫ v = r
  apply pullback.hom_ext («f» := X.hom) («g» := (V).hom)
  · apply (cancel_mono (φ(a)).left).mp
    calc
      _ = nativeAdditiveParameterSection b a ≫ p := by
        simp only [Category.assoc, hp, nativeAdditiveParameterFiberIso_hom_inclusion_assoc]
      _ = p₀ ≫ (φ(a)).left := by
        rw [← nativeAdditiveParameterSection_eq_nativeAffineSection_left]
        exact (isPullback_torusPowerCutPencilProjection_at k g a).w
      _ = _ := by rw [torusPowerCutPencilRetainedEndpoint_fst]
  · simp only [Category.assoc, ht, nativeAdditiveParameterFiberIso_hom_inclusion_assoc]
    have hi : nativeAdditiveParameterSection b a ≫ pullback.fst b (A₁).hom = 𝟙 P :=
      nativeAdditiveParameterSection_fst b a
    change nativeAdditiveParameterSection b a ≫ pullback.fst b (A₁).hom ≫
      (r ≫ pullback.snd X.hom (V).hom) = r ≫ pullback.snd X.hom (V).hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ r ≫ pullback.snd X.hom (V).hom) hi).trans (Category.id_comp _))

end AlgebraicGeometry.Cor
