/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.DeformationPairBaseChange
import Colib.AlgebraicGeometry.Sites.Smooth.AffineLine.CylinderRestriction

/-!
# The deformation fibre maps on an affine étale coordinate chart

A common étale neighborhood identifies the relative motive of an affine
smooth closed pair with that of the coordinate pair pulled back along
its étale map of centres. The cylinder identifications retain the original
fibre arrows at one and zero.
-/

public noncomputable section

set_option quotPrecheck false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.SmoothSite.Contraction
open AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open Stacks.Deformation Stacks.MoreMorphisms

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

attribute [local irreducible] Cor.graphFunctor transferRepresentable

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm(" field ")" =>
  AlgebraicGeometry.Scheme.SmoothSite (Spec (CommRingCat.of field))
local notation "P" => effectivePairMotiveFunctor k

section CoordinateBaseChange

variable (m n : ℕ)

local notation "X₀" => affineSite k (MvPolynomial (Fin m ⊕ Fin n) k)
local notation "Z₀" => affineSite k (MvPolynomial (Fin m) k)
local notation "i₀" => coordinatePairImmersion k m n
local notation "π" => projection (additiveGroupObject (Spec (.of k)))

local instance : IsClosedImmersion (i₀).left := coordinateEmbedding_isClosedImmersion k m n

variable {Z X : Sm(k)} (j : Z ⟶ X) [IsClosedImmersion j.left]
  (a : X ⟶ affineSite k (MvPolynomial (Fin m ⊕ Fin n) k))
  (b : Z ⟶ affineSite k (MvPolynomial (Fin m) k)) [IsAffineHom a.left] [Etale a.left]
  (h : IsPullback j.left b.left a.left (coordinatePairImmersion k m n).left)
  (q : X ⟶ Z)
  (c : IsPullback a.left q.left (coordinateCentreProjection k m n) b.left)

omit [PerfectField k] [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)] [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [IsAffineHom a.left] in
include c in
private theorem isPullback_coordinateDeformationChange :
    IsPullback ((smoothDeformationBaseChange k h ≫
        (coordinateDeformationCylinderOverIso k m n).hom).left)
      (deformationAmbientProjection j ≫ q.left)
      (((π).app X₀).left ≫ coordinateCentreProjection k m n) b.left := by
  have h₀ := (isPullback_deformationMapOver_ambient k h).paste_vert c
  let E := coordinateDeformationCylinderOverIso k m n
  have : IsIso E.hom.left := (forgetScheme _).map_isIso E.hom
  have he' : IsPullback E.hom.left
      (deformationAmbientProjection i₀ ≫ coordinateCentreProjection k m n)
      (((π).app X₀).left ≫ coordinateCentreProjection k m n) (𝟙 (Z₀).left) := by
    let : IsIso (𝟙 (Z₀).left) := (Iso.refl ((Z₀).left)).isIso_hom
    apply IsPullback.of_horiz_isIso
    exact ⟨(coordinateDeformationCylinderIso_centre k m n).trans (Category.comp_id _).symm⟩
  change IsPullback (deformationMapOver h ≫ E.hom.left)
    (deformationAmbientProjection j ≫ q.left)
    (((π).app X₀).left ≫ coordinateCentreProjection k m n) b.left
  have hp := h₀.paste_horiz he'
  have hid : b.left ≫ 𝟙 (Z₀).left = b.left := Category.comp_id _
  exact Eq.mp (congrArg (fun g : Z.left ⟶ (Z₀).left =>
    IsPullback (deformationMapOver h ≫ E.hom.left) (deformationAmbientProjection j ≫ q.left)
      (((π).app X₀).left ≫ coordinateCentreProjection k m n) g) hid) hp

omit [PerfectField k] [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)] [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [IsAffineHom a.left] [Etale a.left] in
include c in
private theorem isPullback_coordinateCylinderChange :
    IsPullback (affineLineCylinder.map a).left (((π).app X).left ≫ q.left)
      (((π).app X₀).left ≫ coordinateCentreProjection k m n) b.left :=
  (affineLineCylinder_map_isPullback a).paste_vert c

private def coordinateDeformationChangeIso :
    closedPairDeformation j ≅ affineLineCylinder.obj X := by
  let h₀ := isPullback_coordinateDeformationChange k m n j a b h q c
  let h₁ := isPullback_coordinateCylinderChange k m n a b q c
  refine MorphismProperty.Over.isoMk (h₀.isoIsPullback _ _ h₁) ?_
  rw [← MorphismProperty.Over.w (affineLineCylinder.map a), ← Category.assoc,
    h₀.isoIsPullback_hom_fst, MorphismProperty.Over.w]

omit [PerfectField k] [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)] [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [IsAffineHom a.left] in
private theorem coordinateDeformationChangeIso_fst :
    (coordinateDeformationChangeIso k m n j a b h q c).hom ≫ affineLineCylinder.map a =
      smoothDeformationBaseChange k h ≫ (coordinateDeformationCylinderOverIso k m n).hom := by
  apply MorphismProperty.Over.Hom.ext
  exact (isPullback_coordinateDeformationChange k m n j a b h q c).isoIsPullback_hom_fst _ _
    (isPullback_coordinateCylinderChange k m n a b q c)

omit [PerfectField k] [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)] [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [IsAffineHom a.left] in
private theorem coordinateDeformationChangeIso_snd :
    (coordinateDeformationChangeIso k m n j a b h q c).hom.left ≫ (((π).app X).left ≫ q.left) =
      deformationAmbientProjection j ≫ q.left := by
  exact (isPullback_coordinateDeformationChange k m n j a b h q c).isoIsPullback_hom_snd _ _
    (isPullback_coordinateCylinderChange k m n a b q c)

private def coordinateCentreBaseChange :
    deformationSupport Z ⟶ deformationSupport Z₀ :=
  homMk (deformationCentreMap (b := b.left)) (by
    change deformationCentreMap (b := b.left) ≫
      (deformationSpaceToBase (⊥ : (Z₀).left.IdealSheafData) ≫ (Z₀).hom) = _
    rw [← Category.assoc, show deformationCentreMap (b := b.left) ≫
        deformationSpaceToBase (⊥ : (Z₀).left.IdealSheafData) =
        deformationSpaceToBase (⊥ : Z.left.IdealSheafData) ≫ b.left from
          deformationMap_toBase _ _ _ _, Category.assoc, MorphismProperty.Over.w b]
    rfl)

omit [PerfectField k] [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)] [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
private theorem isPullback_coordinateSupportChange [Flat b.left] :
    IsPullback ((coordinateCentreBaseChange k m b ≫
        (coordinateSupportCylinderOverIso k m).hom).left)
      (deformationSpaceToBase (⊥ : Z.left.IdealSheafData)) ((π).app Z₀).left b.left := by
  let E := coordinateSupportCylinderOverIso k m
  have : IsIso E.hom.left := (forgetScheme _).map_isIso E.hom
  have he : IsPullback E.hom.left (deformationSpaceToBase (⊥ : (Z₀).left.IdealSheafData))
      ((π).app Z₀).left (𝟙 (Z₀).left) := by
    apply IsPullback.of_horiz_isIso
    exact ⟨(coordinateSupportCylinderIso_projection k m).trans (Category.comp_id _).symm⟩
  change IsPullback (deformationCentreMap (b := b.left) ≫ E.hom.left)
    (deformationSpaceToBase (⊥ : Z.left.IdealSheafData)) ((π).app Z₀).left b.left
  simpa only [Category.comp_id] using (isPullback_deformationCentreMap (b := b.left)).paste_horiz he

private def coordinateSupportChangeIso [Flat b.left] :
    deformationSupport Z ≅ affineLineCylinder.obj Z :=
  cylinderComparisonIso b (coordinateSupportCylinderOverIso k m) (coordinateCentreBaseChange k m b)
    (homMk (deformationSpaceToBase (⊥ : Z.left.IdealSheafData)) rfl)
    (isPullback_coordinateSupportChange k m b)

omit [PerfectField k] [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)] [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
private theorem coordinateSupportChangeIso_snd [Flat b.left] :
    (coordinateSupportChangeIso k m b).hom.left ≫ ((π).app Z).left =
      deformationSpaceToBase (⊥ : Z.left.IdealSheafData) := by
  change ((isPullback_coordinateSupportChange k m b).isoPullback ≪≫
      (affineLineCylinder_map_isPullback b).isoPullback.symm).hom ≫ _ = _
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    (affineLineCylinder_map_isPullback b).isoPullback_inv_snd,
    (isPullback_coordinateSupportChange k m b).isoPullback_hom_snd]

omit [PerfectField k] [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)] [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [IsAffineHom a.left] in
private theorem coordinateSupportChangeIso_comm (hs : j ≫ q = 𝟙 Z) [Flat b.left] :
    (deformationSupportInclusion j).left ≫
        (coordinateDeformationChangeIso k m n j a b h q c).hom.left =
      (coordinateSupportChangeIso k m b).hom.left ≫ (affineLineCylinder.map j).left := by
  let h₁ := isPullback_coordinateCylinderChange k m n a b q c
  apply h₁.hom_ext
  · have hE := congrArg (fun f => f.left) (coordinateDeformationChangeIso_fst k m n j a b h q c)
    have he := congrArg (fun f => f.left)
      (cylinderComparisonIso_hom_map b (coordinateSupportCylinderOverIso k m)
        (coordinateCentreBaseChange k m b)
        (homMk (deformationSpaceToBase (⊥ : Z.left.IdealSheafData)) rfl)
        (isPullback_coordinateSupportChange k m b))
    have hab : j ≫ a = b ≫ i₀ := MorphismProperty.Over.Hom.ext h.w
    have hm : affineLineCylinder.map j ≫ affineLineCylinder.map a =
        affineLineCylinder.map b ≫ affineLineCylinder.map i₀ := by
      rw [← Functor.map_comp, ← Functor.map_comp, hab]
    have hh : (affineLineCylinder.map j).left ≫ (affineLineCylinder.map a).left =
        (affineLineCylinder.map b).left ≫ (affineLineCylinder.map i₀).left :=
      congrArg (fun f : affineLineCylinder.obj Z ⟶ affineLineCylinder.obj X₀ => f.left) hm
    have hD : (deformationSupportInclusion j).left ≫ deformationMapOver h =
        deformationCentreMap (b := b.left) ≫ (deformationSupportInclusion i₀).left :=
      deformationSupportMap_deformationMapOver h
    change (_ ≫ _) ≫ (affineLineCylinder.map a).left =
      (_ ≫ _) ≫ (affineLineCylinder.map a).left
    change (coordinateDeformationChangeIso k m n j a b h q c).hom.left ≫
        (affineLineCylinder.map a).left = deformationMapOver h ≫
          (coordinateDeformationCylinderOverIso k m n).hom.left at hE
    change (coordinateSupportChangeIso k m b).hom.left ≫ (affineLineCylinder.map b).left =
      deformationCentreMap (b := b.left) ≫ (coordinateSupportCylinderOverIso k m).hom.left at he
    rw [Category.assoc, Category.assoc, hE, hh,
      ← Category.assoc _ (affineLineCylinder.map b).left,
      he, Category.assoc, ← Category.assoc (deformationSupportInclusion j).left,
      hD, Category.assoc, coordinateSupportCylinderOverIso_comm k m n]
  · have hjq : j.left ≫ q.left = 𝟙 Z.left := congrArg (fun f : Z ⟶ Z => f.left) hs
    have hproj := (affineLineCylinder_map_isPullback j).w
    change (_ ≫ _) ≫ (((π).app X).left ≫ q.left) =
      (_ ≫ _) ≫ (((π).app X).left ≫ q.left)
    rw [Category.assoc, coordinateDeformationChangeIso_snd, Category.assoc,
      ← Category.assoc (affineLineCylinder.map j).left, hproj, Category.assoc, hjq]
    have hId : (((π).app Z).left ≫ 𝟙 Z.left) = ((π).app Z).left := Category.comp_id _
    rw [hId, coordinateSupportChangeIso_snd]
    change deformationSupportMap j.left ≫
      (deformationSpaceToBase (Stacks.Conormal.coborderIdeal j.left) ≫
        j.left.coborderRange.ι ≫ q.left) = _
    rw [← Category.assoc, deformationSupportMap_toBase, Category.assoc,
      ← Category.assoc j.left.liftCoborder, Scheme.Hom.liftCoborder_ι, hjq, Category.comp_id]

omit [IsAffineHom a.left] in
include h c in
/-- The fibre at one is an equivalence on the original pair pulled back along
an étale map of coordinate centres. -/
theorem isIso_effectivePairMotiveMap_coordinateChangeOne (hs : j ≫ q = 𝟙 Z) :
    IsIso (effectivePairMotiveMap k (deformationOneSquare j)) := by
  let : Etale b.left := MorphismProperty.of_isPullback h (inferInstance : Etale a.left)
  let E := coordinateDeformationChangeIso k m n j a b h q c
  let e := coordinateSupportChangeIso k m b
  let H := coordinateSupportChangeIso_comm k m n j a b h q c hs
  apply isIso_effectivePairMotiveMap_deformationOne_of_cylinder k j
    (closedPairOpenInclusion j.left) (Iso.refl _) (deformationPairCylinderIsoOfMaps k j E e H)
  rw [deformationPairCylinderIsoOfMaps_right]
  change deformationOneMap j ≫ E.hom = 𝟙 X ≫ nativeAffineSection (.of k) X 1
  rw [Category.id_comp]
  apply MorphismProperty.Over.Hom.ext
  apply (isPullback_coordinateCylinderChange k m n a b q c).hom_ext
  · have hr := congrArg (fun f => f.left) (coordinateDeformationChangeIso_fst k m n j a b h q c)
    have hn : (nativeAffineSection (.of k) X 1).left ≫ (affineLineCylinder.map a).left =
        a.left ≫ (nativeAffineSection (.of k) X₀ 1).left :=
      congrArg (fun f => f.left) (nativeAffineSection_naturality (.of k) a 1)
    have hcoord : closedPairOneSection (i₀).left ≫
        (coordinateDeformationCylinderIso k m n).hom = (nativeAffineSection (.of k) X₀ 1).left :=
      coordinateClosedPairOneSection_cylinderIso k m n
    change (closedPairOneSection j.left ≫ E.hom.left) ≫ (affineLineCylinder.map a).left =
      (nativeAffineSection (.of k) X 1).left ≫ (affineLineCylinder.map a).left
    change E.hom.left ≫ (affineLineCylinder.map a).left =
      deformationMapOver h ≫ (coordinateDeformationCylinderIso k m n).hom at hr
    rw [Category.assoc, hr, ← Category.assoc, closedPairOneSection_deformationMapOver h,
      Category.assoc, hcoord, hn]
  · have hn : (nativeAffineSection (.of k) X 1).left ≫ ((π).app X).left = 𝟙 X.left :=
      congrArg (fun f => f.left) (nativeAffineSection_projection (.of k) X 1)
    change (closedPairOneSection j.left ≫ E.hom.left) ≫ (((π).app X).left ≫ q.left) =
      (nativeAffineSection (.of k) X 1).left ≫ (((π).app X).left ≫ q.left)
    have hsec : closedPairOneSection j.left ≫ deformationAmbientProjection j = 𝟙 X.left :=
      closedPairOneSection_toAmbient j.left
    rw [Category.assoc, coordinateDeformationChangeIso_snd, ← Category.assoc,
      hsec, Category.id_comp, ← Category.assoc, hn, Category.id_comp]

set_option maxHeartbeats 500000 in
-- The two pullback identifications are formed using the actual extended-Rees and normal fibres.
omit [IsAffineHom a.left] in
include h c in
/-- The original zero fibre is an equivalence after the same coordinate base change. -/
theorem isIso_effectivePairMotiveMap_coordinateChangeZero (hs : j ≫ q = 𝟙 Z) :
    IsIso (effectivePairMotiveMap k (deformationZeroSquareOfSmooth j)) := by
  let : Etale b.left := MorphismProperty.of_isPullback h (inferInstance : Etale a.left)
  let : Smooth (j.left ≫ X.hom) := smooth_closedPair_comp j
  let : Smooth ((i₀).left ≫ (X₀).hom) := smooth_closedPair_comp i₀
  let : Smooth (coordinateEmbedding k m n ≫ (X₀).hom) := smooth_closedPair_comp i₀
  let E := coordinateDeformationChangeIso k m n j a b h q c
  let e := coordinateSupportChangeIso k m b
  let H := coordinateSupportChangeIso_comm k m n j a b h q c hs
  let N₀ : Stacks.Conormal.normalBundle (i₀).left ≅ (X₀).left :=
    coordinateNormalBundleIso k m n (X₀).hom
  let u := deformationNormalFibreMap h (X₀).hom X.hom
  let ν := Stacks.Conormal.normalBundleToBase j.left
  let ν₀ := Stacks.Conormal.normalBundleToBase (i₀).left
  have hν : normalBundleToDeformation j.left X.hom ≫ deformationAmbientProjection j =
      ν ≫ j.left := normalBundleToDeformation_toAmbient j.left X.hom
  have hν' : normalBundleToDeformation (i₀).left (X₀).hom ≫
      deformationAmbientProjection i₀ = ν₀ ≫ (i₀).left :=
    normalBundleToDeformation_toAmbient (i₀).left (X₀).hom
  have hN₀ : normalBundleToDeformation (i₀).left (X₀).hom ≫
      (coordinateDeformationCylinderIso k m n).hom =
        N₀.hom ≫ (nativeAffineSection (.of k) X₀ 0).left :=
    coordinateNormalBundleToDeformation_cylinderIso k m n (X₀).hom
  have hν₀ : N₀.hom ≫ coordinateCentreProjection k m n = ν₀ := by
    have hsection : (nativeAffineSection (.of k) X₀ 0).left ≫ ((π).app X₀).left =
        𝟙 (X₀).left :=
      congrArg (fun f => f.left) (nativeAffineSection_projection (.of k) X₀ 0)
    have hπ : (coordinateDeformationCylinderIso k m n).hom ≫
        (((π).app X₀).left ≫ coordinateCentreProjection k m n) =
        deformationAmbientProjection i₀ ≫ coordinateCentreProjection k m n :=
      (coordinateDeformationCylinderIso_centre k m n).trans (Category.assoc _ _ _).symm
    have hi : (i₀).left ≫ coordinateCentreProjection k m n = 𝟙 (Z₀).left :=
      coordinateEmbedding_coordinateCentreProjection k m n
    have hw := congrArg (· ≫ (((π).app X₀).left ≫ coordinateCentreProjection k m n)) hN₀
    rw [Category.assoc, hπ, ← Category.assoc, hν', Category.assoc, hi, Category.comp_id,
      Category.assoc, ← Category.assoc (nativeAffineSection (.of k) X₀ 0).left,
      hsection, Category.id_comp] at hw
    exact hw.symm
  have hn : IsPullback (u ≫ N₀.hom) ν
      (coordinateCentreProjection k m n) b.left := by
    have hN := isPullback_deformationNormalFibreMap h (X₀).hom X.hom
    have D := isPullback_deformationMapOver_ambient k h
    have htop : IsPullback u (ν ≫ j.left) (ν₀ ≫ (i₀).left) a.left := by
      rw [← hν, ← hν']
      exact hN.flip.paste_vert D
    have hj : j.left ≫ q.left = 𝟙 Z.left := congrArg (fun f : Z ⟶ Z => f.left) hs
    have hi : (i₀).left ≫ coordinateCentreProjection k m n = 𝟙 (Z₀).left :=
      coordinateEmbedding_coordinateCentreProjection k m n
    have hh : IsPullback u ν ν₀ b.left := by
      have hw := htop.paste_vert c
      rw [Category.assoc, hj, Category.comp_id, Category.assoc, hi, Category.comp_id] at hw
      exact hw
    let : IsIso N₀.hom := N₀.isIso_hom
    have he₀ : IsPullback N₀.hom ν₀ (coordinateCentreProjection k m n) (𝟙 (Z₀).left) :=
      IsPullback.of_horiz_isIso ⟨hν₀.trans (Category.comp_id _).symm⟩
    have hw := hh.paste_horiz he₀
    have hid : b.left ≫ 𝟙 (Z₀).left = b.left := Category.comp_id _
    exact hid ▸ hw
  let N : normalBundleOfSmooth j ≅ X := MorphismProperty.Over.isoMk
    (hn.isoIsPullback _ _ c) (by
      rw [← MorphismProperty.Over.w q, ← Category.assoc, hn.isoIsPullback_hom_snd]
      rfl)
  have hN₁ : N.hom.left ≫ a.left = u ≫ N₀.hom := hn.isoIsPullback_hom_fst _ _ c
  have hN₂ : N.hom.left ≫ q.left = ν := hn.isoIsPullback_hom_snd _ _ c
  let z := actualNormalZeroSection j.left
  have hz : z ≫ N.hom.left = j.left := by
    apply c.hom_ext
    · have hZ : z ≫ u = b.left ≫ actualNormalZeroSection (i₀).left :=
        deformationNormalFibreMap_zeroSection h (X₀).hom X.hom
      have hzero : actualNormalZeroSection (i₀).left ≫ N₀.hom = (i₀).left :=
        coordinateNormalBundleIso_zeroSection k m n (X₀).hom
      rw [Category.assoc, hN₁, ← Category.assoc, hZ, Category.assoc, hzero]
      exact h.w.symm
    · have hzν : z ≫ ν = 𝟙 Z.left :=
        Scheme.Modules.vectorBundleZeroSection_comp_vectorBundleToBase _ _
      exact (Category.assoc _ _ _).trans ((congrArg (z ≫ ·) hN₂).trans (hzν.trans
        (congrArg (fun f : Z ⟶ Z => f.left) hs).symm))
  let : IsIso N.hom.left := (forgetScheme _).map_isIso N.hom
  have hZ : IsPullback z (𝟙 Z.left) N.hom.left j.left :=
    IsPullback.of_vert_isIso ⟨hz.trans (Category.id_comp _).symm⟩
  let s := closedPairSquare (f := N.hom) hZ
  let : IsIso s.f₃₄ := inferInstanceAs (IsIso N.hom)
  let A := openPairArrowIsoOfAmbientIso s (closedPairSquare_isPullback (f := N.hom) hZ)
  apply isIso_effectivePairMotiveMap_deformationZero_of_cylinder k j
    (closedPairOpenInclusion j.left) A (deformationPairCylinderIsoOfMaps k j E e H)
  rw [deformationPairCylinderIsoOfMaps_right]
  have hA : A.hom.right = N.hom :=
    openPairArrowIsoOfAmbientIso_right _ (closedPairSquare_isPullback (f := N.hom) hZ)
  rw [hA]
  apply MorphismProperty.Over.Hom.ext
  apply (isPullback_coordinateCylinderChange k m n a b q c).hom_ext
  · have ht : normalBundleToDeformation j.left X.hom ≫ deformationMapOver h =
        u ≫ normalBundleToDeformation (i₀).left (X₀).hom :=
      (isPullback_deformationNormalFibreMap h (X₀).hom X.hom).w
    have hE := congrArg (fun f => f.left) (coordinateDeformationChangeIso_fst k m n j a b h q c)
    have hnat : (nativeAffineSection (.of k) X 0).left ≫ (affineLineCylinder.map a).left =
        a.left ≫ (nativeAffineSection (.of k) X₀ 0).left :=
      congrArg (fun f => f.left) (nativeAffineSection_naturality (.of k) a 0)
    change (Stacks.Deformation.normalBundleToDeformation j.left X.hom ≫ E.hom.left) ≫
        (affineLineCylinder.map a).left =
        (N.hom.left ≫ (nativeAffineSection (.of k) X 0).left) ≫
          (affineLineCylinder.map a).left
    change E.hom.left ≫ (affineLineCylinder.map a).left =
      deformationMapOver h ≫ (coordinateDeformationCylinderIso k m n).hom at hE
    rw [Category.assoc, hE, ← Category.assoc, ht, Category.assoc,
      hN₀, Category.assoc, hnat, ← Category.assoc N.hom.left, hN₁, Category.assoc]
  · have hnat : (nativeAffineSection (.of k) X 0).left ≫ ((π).app X).left = 𝟙 X.left :=
      congrArg (fun f => f.left) (nativeAffineSection_projection (.of k) X 0)
    have hjq : j.left ≫ q.left = 𝟙 Z.left := congrArg (fun f : Z ⟶ Z => f.left) hs
    change (Stacks.Deformation.normalBundleToDeformation j.left X.hom ≫ E.hom.left) ≫
        (((π).app X).left ≫ q.left) =
        (N.hom.left ≫ (nativeAffineSection (.of k) X 0).left) ≫ (((π).app X).left ≫ q.left)
    rw [Category.assoc, coordinateDeformationChangeIso_snd, ← Category.assoc,
      hν, Category.assoc, hjq, Category.comp_id,
      Category.assoc, ← Category.assoc (nativeAffineSection (.of k) X 0).left,
      hnat, Category.id_comp, hN₂]

end CoordinateBaseChange

section MarkedTrivialChart

variable (m n : ℕ)

local notation "X₀" => affineSite k (MvPolynomial (Fin m ⊕ Fin n) k)
local notation "Z₀" => affineSite k (MvPolynomial (Fin m) k)
local notation "i₀" => coordinatePairImmersion k m n

local instance : IsClosedImmersion (i₀).left := coordinateEmbedding_isClosedImmersion k m n

set_option maxHeartbeats 700000 in
-- The two affine pullbacks elaborate through the explicit affine spectrum identifications.
/-- Both fibre maps on an affine smooth coordinate chart are isomorphisms.
The étale coordinate map is allowed to be nontrivial on its centre. -/
theorem isIso_effectivePairMotiveMap_of_affineEtaleCoordinates
    {Z X : Sm(k)} (i : Z ⟶ X) [IsClosedImmersion i.left] [IsAffine X.left] [IsAffine Z.left]
    (a : X ⟶ X₀) (b : Z ⟶ Z₀) [Etale a.left]
    (h : IsPullback i.left b.left a.left (i₀).left) :
    IsIso (effectivePairMotiveMap k (deformationOneSquare i)) ∧
      IsIso (effectivePairMotiveMap k (deformationZeroSquareOfSmooth i)) := by
  let q₀ := coordinateCentreProjection k m n
  let Y := pullback q₀ b.left
  let f : Y ⟶ (X₀).left := pullback.fst q₀ b.left
  let : IsAffine (X₀).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) k))))
  let q : Y ⟶ Z.left := pullback.snd q₀ b.left
  let : IsAffine (Z₀).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin m) k))))
  let : IsAffineHom q₀ := isAffineHom_of_isAffine q₀
  let : IsAffine Y := inferInstanceAs (IsAffine (pullback q₀ b.left))
  let : Smooth q₀ := smooth_coordinateCentreProjection k m n
  let : Smooth q := MorphismProperty.pullback_snd q₀ b.left (inferInstance : Smooth q₀)
  let : Etale b.left := MorphismProperty.of_isPullback h (inferInstance : Etale a.left)
  let : Etale f := MorphismProperty.pullback_fst q₀ b.left (inferInstance : Etale b.left)
  let Yₛ : Sm(k) := mk (q ≫ Z.hom)
  let Q : Yₛ ⟶ Z := homMk q rfl
  have hc := (IsPullback.of_hasPullback q₀ b.left).w
  let F : Yₛ ⟶ X₀ := homMk f (by
    have h₀ : q₀ ≫ (Z₀).hom = (X₀).hom := by
      dsimp only [q₀]
      unfold coordinateCentreProjection
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      exact MvPolynomial.rename_C _ _
    change f ≫ (X₀).hom = q ≫ Z.hom
    rw [← h₀, ← Category.assoc, hc, Category.assoc, MorphismProperty.Over.w b])
  let t : Z.left ⟶ Y := pullback.lift (b.left ≫ (i₀).left) (𝟙 Z.left) (by
    have hcoord : (i₀).left ≫ q₀ = 𝟙 (Z₀).left :=
      coordinateEmbedding_coordinateCentreProjection k m n
    rw [Category.assoc, hcoord, Category.comp_id, Category.id_comp])
  have htq : t ≫ q = 𝟙 Z.left := pullback.lift_snd _ _ _
  have htf : t ≫ f = b.left ≫ (i₀).left := pullback.lift_fst _ _ _
  let : IsSeparated q := inferInstance
  have htq' : IsClosedImmersion (t ≫ q) := htq.symm ▸ inferInstance
  let : IsClosedImmersion t := IsClosedImmersion.of_comp t q
  let T : Z ⟶ Yₛ := homMk t (by
    change t ≫ q ≫ Z.hom = Z.hom
    rw [← Category.assoc, htq, Category.id_comp])
  let : IsClosedImmersion T.left := inferInstanceAs (IsClosedImmersion t)
  let : IsAffine Yₛ.left := inferInstanceAs (IsAffine Y)
  let : IsAffineHom F.left := isAffineHom_of_isAffine f
  let : Etale F.left := inferInstanceAs (Etale f)
  have hTQ : T ≫ Q = 𝟙 Z := MorphismProperty.Over.Hom.ext htq
  have htc : IsPullback T.left b.left F.left (i₀).left := by
    let d := IsPullback.of_hasPullback q₀ b.left
    have hi₀ : (i₀).left ≫ q₀ = 𝟙 (Z₀).left :=
      coordinateEmbedding_coordinateCentreProjection k m n
    have H : IsPullback (T.left ≫ q) b.left b.left ((i₀).left ≫ q₀) := by
      change IsPullback (t ≫ q) b.left b.left ((i₀).left ≫ q₀)
      rw [htq, hi₀]
      exact IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩
    exact H.of_right htf d.flip
  have hY₁ := isIso_effectivePairMotiveMap_coordinateChangeOne k m n T F b htc Q
    (IsPullback.of_hasPullback q₀ b.left) hTQ
  have hY₀ := isIso_effectivePairMotiveMap_coordinateChangeZero k m n T F b htc Q
    (IsPullback.of_hasPullback q₀ b.left) hTQ
  obtain ⟨W, hW, l, r, s, hl, hr, hcompat, hsl, hsr, hleft, hright⟩ :=
    exists_affine_common_etale_neighborhood i.left T.left a.left F.left (h.w.trans htf.symm)
  let : IsAffine W := hW
  let : Etale l := hl
  let : Etale r := hr
  let Wₛ := mk (l ≫ X.hom)
  let : IsAffine Wₛ.left := inferInstanceAs (IsAffine W)
  let L : Wₛ ⟶ X := homMk l rfl
  let : IsAffineHom L.left := inferInstanceAs (IsAffineHom l)
  let : Etale L.left := inferInstanceAs (Etale l)
  let Re : Wₛ ⟶ Yₛ := homMk r (by
    change r ≫ Yₛ.hom = l ≫ X.hom
    rw [← MorphismProperty.Over.w F, ← Category.assoc, ← hcompat, Category.assoc,
      MorphismProperty.Over.w a])
  let : IsAffineHom Re.left := inferInstanceAs (IsAffineHom r)
  let : Etale Re.left := inferInstanceAs (Etale r)
  let S₁ : Z ⟶ Wₛ := homMk s (by
    change s ≫ l ≫ X.hom = Z.hom
    rw [← Category.assoc, hsl, MorphismProperty.Over.w i])
  let : IsClosedImmersion S₁.left := MorphismProperty.of_isPullback hleft.flip inferInstance
  let z : Z ⟶ Z := 𝟙 Z
  let : IsIso z.left := inferInstanceAs (IsIso (𝟙 Z.left))
  have hL : IsPullback S₁.left z.left L.left i.left := hleft
  have hR : IsPullback S₁.left z.left Re.left T.left := hright
  exact ⟨(isIso_effectivePairMotiveMap_deformationOne_iff_of_etale k hL).mp
      ((isIso_effectivePairMotiveMap_deformationOne_iff_of_etale k hR).mpr hY₁),
    (isIso_effectivePairMotiveMap_deformationZero_iff_of_etale k hL).mp
      ((isIso_effectivePairMotiveMap_deformationZero_iff_of_etale k hR).mpr hY₀)⟩

end MarkedTrivialChart

end AlgebraicGeometry.MotivicHomotopy
