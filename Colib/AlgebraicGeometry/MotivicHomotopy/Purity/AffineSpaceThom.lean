/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.TrivialThomPower

/-! # Naturality of the normalized supported motive of affine space -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

private theorem mapIso_symm_trans_hom {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B : C} {K : D} (e : A ≅ B) (f : F.obj A ≅ K) :
    ((F.mapIso e).symm ≪≫ f).hom = F.map e.inv ≫ f.hom :=
  rfl

private theorem map_iso_comp_naturality {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A A' B B' : C} {X Y : D}
    (a : A ⟶ A') (b : B ⟶ B') (x : A ≅ B) (y : A' ≅ B')
    (e : F.obj A ⟶ X) (e' : F.obj A' ⟶ Y) (f : X ⟶ Y)
    (h : b ≫ y.inv = x.inv ≫ a) (he : F.map a ≫ e' = e ≫ f) :
    F.map b ≫ (F.map y.inv ≫ e') = (F.map x.inv ≫ e) ≫ f := by
  rw [← F.map_comp_assoc, h, F.map_comp, Category.assoc, he, Category.assoc]

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S
local notation "M" => effectiveSmoothMotive k
local notation "T(" n ")" => Stabilization.iterate (effectiveLefschetzTwistFunctor k) n
local notation "Φ" => effectivePairMotiveFunctor k

attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable
  affineCylinderPowerSupportIso effectiveTrivialPowerThomIso

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 650000 in
-- Identify the component of the original comparison with the marked tower.
private theorem effectiveAffineSpaceThomIso_hom (X : Sm) [IsAffine X.left] (n : ℕ) :
    (effectiveAffineSpaceThomIso k X n).hom =
      (Φ).map (affineCylinderPowerSupportIso k X n).inv ≫
        (effectiveTrivialPowerThomIso k X n).hom := by
  unfold effectiveAffineSpaceThomIso
  exact mapIso_symm_trans_hom (Φ) (affineCylinderPowerSupportIso k X n)
    (effectiveTrivialPowerThomIso k X n)

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1000000 in
-- Paste the original arrow comparison with the naturality of the marked tower.
/-- The same supported comparison under the original affine-space map.
The compatibility of the marked towers identifies the two coordinate maps. -/
theorem effectiveAffineSpaceThomIso_naturality {X Y : Sm} [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) (n : ℕ) :
    let b := closedSupportArrowMap
      (i := relativeAffineSpaceZeroSection X n) (j := relativeAffineSpaceZeroSection Y n)
      (f := affineSpaceObjectMap f n) (g := f) (affineSpaceOrigin_isPullback f n)
    (Φ).map b ≫ (effectiveAffineSpaceThomIso k Y n).hom =
      (effectiveAffineSpaceThomIso k X n).hom ≫ (T(n)).map ((M).map f) := by
  intro b
  let a := closedSupportArrowMap
    (i := affineCylinderPowerZero k X n) (j := affineCylinderPowerZero k Y n)
    (f := affineCylinderPowerMap k f n) (g := f) (affineCylinderPowerZero_isPullback k f n)
  let x := affineCylinderPowerSupportIso k X n
  let y := affineCylinderPowerSupportIso k Y n
  let e := (effectiveTrivialPowerThomIso k X n).hom
  let e' := (effectiveTrivialPowerThomIso k Y n).hom
  let d := (T(n)).map ((M).map f)
  have h : b ≫ y.inv = x.inv ≫ a := affineCylinderPowerSupportIso_inv_naturality k f n
  have he : (Φ).map a ≫ e' = e ≫ d := effectiveTrivialPowerThomIso_naturality k f n
  have ht : (Φ).map b ≫ ((Φ).map y.inv ≫ e') = ((Φ).map x.inv ≫ e) ≫ d :=
    map_iso_comp_naturality (Φ) a b x y e e' d h he
  have hx : (effectiveAffineSpaceThomIso k X n).hom = (Φ).map x.inv ≫ e :=
    effectiveAffineSpaceThomIso_hom k X n
  have hy : (effectiveAffineSpaceThomIso k Y n).hom = (Φ).map y.inv ≫ e' :=
    effectiveAffineSpaceThomIso_hom k Y n
  exact (congrArg ((Φ).map b ≫ ·) hy).trans (ht.trans (congrArg (· ≫ d) hx.symm))

set_option maxHeartbeats 650000 in
-- Compose the affine comparison with the original base structure map.
/-- The normalized class restricts to the normalized class on the original base change. -/
theorem effectiveAffineSpaceThomClass_naturality {X Y : Sm}
    [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) (n : ℕ) :
    effectiveMotiveWithSupportMap k
      (i := relativeAffineSpaceZeroSection X n) (j := relativeAffineSpaceZeroSection Y n)
      (f := affineSpaceObjectMap f n) (g := f)
      (affineSpaceOrigin_isPullback f n) ≫
      effectiveAffineSpaceThomClass k Y n = effectiveAffineSpaceThomClass k X n := by
  unfold effectiveAffineSpaceThomClass
  rw [← Category.assoc, effectiveAffineSpaceThomIso_naturality k f n, Category.assoc,
    ← (T(n)).map_comp, ← (M).map_comp, comp_toBase]

end AlgebraicGeometry.MotivicHomotopy
