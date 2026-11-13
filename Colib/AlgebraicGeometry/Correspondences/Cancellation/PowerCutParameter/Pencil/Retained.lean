/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.Pencil
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.RetainedPowerCutSupport

/-!
# The closed support of the pencil with both old coordinates retained

Move the old source torus to the retained target before extending the support
by the affine parameter. This gives a closed immersion of the whole pencil
support. Its two projections are the pencil projection and the pullback of
the original retained target map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))} {P : Scheme.{u}}
  (j : P ⟶ pullback
    (SmoothSite.product X (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom
    (SmoothSite.product Y (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom)

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => multiplicativeGroupObject Sₖ
local notation "A₁" => (additiveGroupObject Sₖ)
local notation "XG" => (product X Gₘ)
local notation "YG" => (product Y Gₘ)
local notation "V" => (torusPowerCutRetainedTarget k Y)
local notation "B" => (product X A₁)
set_option quotPrecheck false in
local notation "g" => (j ≫ pullback.fst (XG).hom (YG).hom)
set_option quotPrecheck false in
local notation "r" => (j ≫ (torusPowerCutAmbientSchemeIso k X Y).hom)
set_option quotPrecheck false in
local notation "b" => (g ≫ (XG).hom)
set_option quotPrecheck false in
local notation "bR" => (r ≫ (product X V).hom)
set_option quotPrecheck false in
local notation "π" => pullback.fst b (A₁).hom

/-- The retained support has the same structural map to the coefficient field. -/
theorem torusPowerCutPencilRetainedSupport_structureMap : b = bR := by
  change (j ≫ (productFst XG YG).left) ≫ (XG).hom =
    (j ≫ (torusPowerCutAmbientIso k X Y).hom.left) ≫ (product X V).hom
  calc
    _ = j ≫ (product XG YG).hom := Category.assoc _ _ _
    _ = j ≫ (torusPowerCutAmbientIso k X Y).hom.left ≫ (product X V).hom :=
      congrArg (fun m => j ≫ m) (MorphismProperty.Over.w (torusPowerCutAmbientIso k X Y).hom).symm
    _ = _ := (Category.assoc _ _ _).symm

/-- The whole pencil support with its original two torus coordinates on the target. -/
def torusPowerCutPencilRetainedSupportMap : pullback b (A₁).hom ⟶ pullback (B).hom (V).hom :=
  (pullback.congrHom (torusPowerCutPencilRetainedSupport_structureMap k j) rfl).hom ≫
    supportParameterExtension r A₁

instance torusPowerCutPencilRetainedSupportMap_isClosedImmersion [IsClosedImmersion j] :
    IsClosedImmersion (torusPowerCutPencilRetainedSupportMap k j) := by
  let : IsClosedImmersion r := inferInstance
  unfold torusPowerCutPencilRetainedSupportMap
  infer_instance

/-- The retained closed support still projects by the actual finite pencil map. -/
@[reassoc] theorem torusPowerCutPencilRetainedSupportMap_fst :
    torusPowerCutPencilRetainedSupportMap k j ≫ pullback.fst (B).hom (V).hom =
      torusPowerCutPencilProjection k g := by
  have h := congrArg (fun m => m.left) (torusPowerCutAmbientIso_hom_source k X Y)
  change (torusPowerCutAmbientIso k X Y).hom.left ≫ (productFst X V).left =
    (productFst XG YG).left ≫ (productFst X Gₘ).left at h
  apply pullback.hom_ext (f := X.hom) («g» := (A₁).hom)
  · change (torusPowerCutPencilRetainedSupportMap k j ≫ (productFst B V).left) ≫
      (productFst X A₁).left = torusPowerCutPencilProjection k g ≫ (productFst X A₁).left
    simp only [torusPowerCutPencilRetainedSupportMap, torusPowerCutPencilProjection, Category.assoc,
      supportParameterExtension_base, pullback.congrHom_hom, pullback.map, pullback.lift_fst_assoc,
      Category.id_comp, torusPowerCutAmbientSchemeIso, Functor.mapIso_hom]
    exact congrArg (fun v => π ≫ j ≫ v) h
  · change (torusPowerCutPencilRetainedSupportMap k j ≫ (productFst B V).left) ≫
      (productSnd X A₁).left = torusPowerCutPencilProjection k g ≫ (productSnd X A₁).left
    simp only [torusPowerCutPencilRetainedSupportMap, torusPowerCutPencilProjection, Category.assoc,
      supportParameterExtension_parameter, pullback.congrHom_hom, pullback.map]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The retained target map is the original one pulled back to the pencil support. -/
@[reassoc] theorem torusPowerCutPencilRetainedSupportMap_snd :
    torusPowerCutPencilRetainedSupportMap k j ≫ pullback.snd (B).hom (V).hom =
      π ≫ r ≫ pullback.snd X.hom (V).hom := by
  change torusPowerCutPencilRetainedSupportMap k j ≫ (productSnd B V).left =
    π ≫ r ≫ (productSnd X V).left
  simp only [torusPowerCutPencilRetainedSupportMap, Category.assoc,
    supportParameterExtension_oldFactor, pullback.congrHom_hom, pullback.map,
    pullback.lift_fst_assoc, Category.id_comp]

end AlgebraicGeometry.Cor
