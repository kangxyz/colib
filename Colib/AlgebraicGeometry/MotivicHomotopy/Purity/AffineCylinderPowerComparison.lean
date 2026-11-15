/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineCylinderPower
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineLineMarkedComparison
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineSpaceZero

/-! # The marked cylinder tower as a literal affine space -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]

set_option quotPrecheck false in
local notation "S" => Spec (CommRingCat.of k)

/-- Split off the last coordinate of affine space. -/
def affineSpaceSuccLastIso (X : Scheme.{u}) (n : ℕ) :
    AffineSpace (ULift.{u} (Fin (n + 1))) X ≅
      AffineSpace (ULift.{u} (Fin 1)) (AffineSpace (ULift.{u} (Fin n)) X) :=
  Stacks.Chow.affineSpaceReindexIso
    ((Stacks.Chow.uliftFinSuccSumEquiv.{u} n).trans (Equiv.sumComm _ _)) X ≪≫
    Stacks.Chow.affineSpaceSumIso (ULift.{u} (Fin 1)) (ULift.{u} (Fin n)) X

/-- The comparison of the cylinder tower with affine space, together with its zero equation. -/
def affineCylinderPowerMarkedComparison (X : SmoothSite S) [IsAffine X.left] (n : ℕ) :
    { e : affineCylinderPower k X n ≅ SmoothSite.relativeAffineSpace X n //
      affineCylinderPowerZero k X n ≫ e.hom = SmoothSite.relativeAffineSpaceZeroSection X n } := by
  induction n with
  | zero =>
      let p : AffineSpace (ULift.{u} (Fin 0)) X.left ⟶ X.left :=
        AffineSpace (ULift.{u} (Fin 0)) X.left ↘ X.left
      let e := asIso p
      refine ⟨MorphismProperty.Over.isoMk e.symm ?_, ?_⟩
      · change e.inv ≫ p ≫ X.hom = X.hom
        exact e.inv_hom_id_assoc _
      · apply MorphismProperty.Over.Hom.ext
        change 𝟙 X.left ≫ e.inv = AffineSpace.origin X.left _
        rw [Category.id_comp, ← cancel_mono p]
        exact e.inv_hom_id.trans (AffineSpace.origin_over _ _).symm
  | succ n ih =>
      let Y := affineCylinderPower k X n
      let Z := AffineSpace (ULift.{u} (Fin n)) X.left
      let b : Y.left ≅ Z := (SmoothSite.forgetScheme S).mapIso ih.val
      letI : IsAffine Y.left := IsAffine.of_isIso b.hom
      let c := nativeAffineCylinderAffineSpaceIso Y
      let f := AffineSpace.map (ULift.{u} (Fin 1)) b.hom
      letI : IsIso f :=
        (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) b.hom).isIso_fst_of_isIso
      let a := affineSpaceSuccLastIso X.left n
      let e := c ≪≫ asIso f ≪≫ a.symm
      have ha :
          a.inv ≫ (AffineSpace (ULift.{u} (Fin (n + 1))) X.left ↘ X.left) =
            (AffineSpace (ULift.{u} (Fin 1)) Z ↘ Z) ≫ (Z ↘ X.left) := by
        rw [← AffineSpace.affineSpaceSuccLastIso_hom_over X.left n]
        exact a.inv_hom_id_assoc _
      refine ⟨MorphismProperty.Over.isoMk e ?_, ?_⟩
      · change (c.hom ≫ f ≫ a.inv) ≫
          (AffineSpace (ULift.{u} (Fin (n + 1))) X.left ↘ X.left) ≫ X.hom = _
        have hb : b.hom ≫ (Z ↘ X.left) ≫ X.hom = Y.hom :=
          MorphismProperty.Over.w ih.val.hom
        let π := (projection (SmoothSite.additiveGroupObject S)).app Y
        have hf : f ≫ (AffineSpace (ULift.{u} (Fin 1)) Z ↘ Z) ≫ (Z ↘ X.left) ≫ X.hom =
            (AffineSpace (ULift.{u} (Fin 1)) Y.left ↘ Y.left) ≫ Y.hom := by
          change AffineSpace.map (ULift.{u} (Fin 1)) b.hom ≫ _ = _
          rw [AffineSpace.map_over_assoc, hb]
        have hc : c.hom ≫ (AffineSpace (ULift.{u} (Fin 1)) Y.left ↘ Y.left) ≫ Y.hom =
            π.left ≫ Y.hom :=
          nativeAffineCylinderAffineSpaceIso_hom_over_assoc Y _
        simp only [Category.assoc, reassoc_of% ha, hf, hc]
        exact MorphismProperty.Over.w π
      · apply MorphismProperty.Over.Hom.ext
        change ((affineCylinderPowerZero k X n).left ≫
          (nativeAffineSection (.of k) Y 0).left) ≫ c.hom ≫ f ≫ a.inv =
            AffineSpace.origin X.left _
        have hz : (affineCylinderPowerZero k X n).left ≫ b.hom =
            AffineSpace.origin X.left (ULift.{u} (Fin n)) :=
          congrArg (fun g => g.left) ih.property
        apply (cancel_mono a.hom).1
        simp only [Category.assoc, a.inv_hom_id]
        rw [nativeAffineCylinderAffineSpaceIso_zero_assoc]
        change (affineCylinderPowerZero k X n).left ≫
          AffineSpace.origin Y.left (ULift.{u} (Fin 1)) ≫
            AffineSpace.map (ULift.{u} (Fin 1)) b.hom = _
        rw [AffineSpace.origin_map, ← Category.assoc, hz]
        exact (AffineSpace.origin_affineSpaceSuccLastIso X.left n).symm

/-- Over an affine smooth scheme, the successive native cylinders give the literal
relative affine space with one coordinate for each factor. -/
def affineCylinderPowerAffineSpaceIso (X : SmoothSite S) [IsAffine X.left] (n : ℕ) :
    affineCylinderPower k X n ≅ SmoothSite.relativeAffineSpace X n :=
  (affineCylinderPowerMarkedComparison k X n).val

/-- The successive native zero sections give the literal affine-space origin. -/
@[reassoc]
theorem affineCylinderPowerAffineSpaceIso_zero
    (X : SmoothSite S) [IsAffine X.left] (n : ℕ) :
    affineCylinderPowerZero k X n ≫ (affineCylinderPowerAffineSpaceIso k X n).hom =
      SmoothSite.relativeAffineSpaceZeroSection X n :=
  (affineCylinderPowerMarkedComparison k X n).property

private theorem affineSpaceSuccLastIso_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    AffineSpace.map (ULift.{u} (Fin (n + 1))) f ≫ (affineSpaceSuccLastIso Y n).hom =
      (affineSpaceSuccLastIso X n).hom ≫
        AffineSpace.map (ULift.{u} (Fin 1)) (AffineSpace.map (ULift.{u} (Fin n)) f) := by
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, affineSpaceSuccLastIso, Iso.trans_hom,
      Stacks.Chow.affineSpaceSumIso_hom_over, AffineSpace.map_over,
      Stacks.Chow.affineSpaceReindexIso]
    simp only [AffineSpace.map_reindex_assoc, AffineSpace.map_reindex,
      reassoc_of% Stacks.Chow.affineSpaceSumIso_hom_over]
  · intro j
    simp only [Category.assoc, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      affineSpaceSuccLastIso, Iso.trans_hom, Stacks.Chow.affineSpaceReindexIso,
      Stacks.Chow.affineSpaceSumIso, AffineSpace.homOfVector_appTop_coord,
      AffineSpace.reindex_appTop_coord, AffineSpace.map_appTop_coord]

set_option maxHeartbeats 1200000 in
-- The successor unfolds the recursive site isomorphisms and their underlying scheme maps.
/-- The marked tower comparison commutes with the original maps between affine bases. -/
@[reassoc]
theorem affineCylinderPowerAffineSpaceIso_naturality {X Y : SmoothSite S}
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) (n : ℕ) :
    affineCylinderPowerMap k f n ≫ (affineCylinderPowerAffineSpaceIso k Y n).hom =
      (affineCylinderPowerAffineSpaceIso k X n).hom ≫ SmoothSite.affineSpaceObjectMap f n := by
  apply MorphismProperty.Over.Hom.ext
  induction n with
  | zero =>
      change f.left ≫ inv (AffineSpace (ULift.{u} (Fin 0)) Y.left ↘ Y.left) =
        inv (AffineSpace (ULift.{u} (Fin 0)) X.left ↘ X.left) ≫
          AffineSpace.map (ULift.{u} (Fin 0)) f.left
      apply (cancel_mono (AffineSpace (ULift.{u} (Fin 0)) Y.left ↘ Y.left)).1
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
        AffineSpace.map_over, IsIso.inv_hom_id_assoc]
  | succ n ih =>
      let U := affineCylinderPower k X n
      let V := affineCylinderPower k Y n
      let g : U ⟶ V := affineCylinderPowerMap k f n
      let bX : U.left ≅ AffineSpace (ULift.{u} (Fin n)) X.left :=
        (SmoothSite.forgetScheme S).mapIso (affineCylinderPowerAffineSpaceIso k X n)
      let bY : V.left ≅ AffineSpace (ULift.{u} (Fin n)) Y.left :=
        (SmoothSite.forgetScheme S).mapIso (affineCylinderPowerAffineSpaceIso k Y n)
      let : IsAffine U.left := IsAffine.of_isIso bX.hom
      let : IsAffine V.left := IsAffine.of_isIso bY.hom
      let cX := nativeAffineCylinderAffineSpaceIso U
      let cY := nativeAffineCylinderAffineSpaceIso V
      let aX := affineSpaceSuccLastIso X.left n
      let aY := affineSpaceSuccLastIso Y.left n
      have h : g.left ≫ bY.hom = bX.hom ≫ AffineSpace.map (ULift.{u} (Fin n)) f.left := ih
      change (affineLineCylinder.map g).left ≫
          (cY.hom ≫ AffineSpace.map (ULift.{u} (Fin 1)) bY.hom ≫ aY.inv) =
        (cX.hom ≫ AffineSpace.map (ULift.{u} (Fin 1)) bX.hom ≫ aX.inv) ≫
          AffineSpace.map (ULift.{u} (Fin (n + 1))) f.left
      apply (cancel_mono aY.hom).1
      simp only [Category.assoc, aY.inv_hom_id]
      rw [nativeAffineCylinderAffineSpaceIso_naturality_assoc, Category.comp_id,
        ← AffineSpace.map_comp, h, AffineSpace.map_comp]
      have ha := affineSpaceSuccLastIso_naturality f.left n
      change _ ≫ aY.hom = aX.hom ≫ _ at ha
      rw [ha, aX.inv_hom_id_assoc]

end AlgebraicGeometry.MotivicHomotopy
