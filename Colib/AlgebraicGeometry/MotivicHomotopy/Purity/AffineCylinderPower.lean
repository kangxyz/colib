/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.NativeSections
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineSectionNaturality
public import Colib.AlgebraicGeometry.Sites.Smooth.AffineLine.CylinderRestriction

/-! # Powers of the original affine cylinder with its zero section -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]

local notation "Sm(" k ")" => SmoothSite (Spec (CommRingCat.of k))

/-- The literal cylinder with one copy of the native affine line in each coordinate. -/
def affineCylinderPower (X : Sm(k)) : ℕ → Sm(k)
  | 0 => X
  | n + 1 => affineLineCylinder.obj (affineCylinderPower X n)

/-- The zero section is the succession of the original native zero sections. -/
def affineCylinderPowerZero (X : Sm(k)) (n : ℕ) : X ⟶ affineCylinderPower k X n :=
  match n with
  | 0 => 𝟙 X
  | n + 1 =>
    affineCylinderPowerZero X n ≫ nativeAffineSection (.of k) (affineCylinderPower k X n) 0

instance affineCylinderPowerZero_isClosedImmersion (X : Sm(k)) (n : ℕ) :
    IsClosedImmersion (affineCylinderPowerZero k X n).left := by
  induction n with
  | zero => exact inferInstanceAs (IsClosedImmersion (𝟙 X.left))
  | succ n ih =>
    let := ih
    change IsClosedImmersion ((affineCylinderPowerZero k X n).left ≫
      (nativeAffineSection (.of k) (affineCylinderPower k X n) 0).left)
    infer_instance

/-- The original parameter maps applied one coordinate at a time. -/
def affineCylinderPowerMap {X Y : Sm(k)} (f : X ⟶ Y) (n : ℕ) :
    affineCylinderPower k X n ⟶ affineCylinderPower k Y n :=
  match n with
  | 0 => f
  | n + 1 => affineLineCylinder.map (affineCylinderPowerMap f n)

/-- The original map on powers preserves the zero coordinates. -/
@[reassoc]
theorem affineCylinderPowerZero_naturality {X Y : Sm(k)} (f : X ⟶ Y) (n : ℕ) :
    affineCylinderPowerZero k X n ≫ affineCylinderPowerMap k f n =
      f ≫ affineCylinderPowerZero k Y n := by
  induction n with
  | zero => exact (Category.id_comp f).trans (Category.comp_id f).symm
  | succ n ih =>
    change (affineCylinderPowerZero k X n ≫ nativeAffineSection (.of k) _ 0) ≫
      affineLineCylinder.map (affineCylinderPowerMap k f n) =
        f ≫ affineCylinderPowerZero k Y n ≫ nativeAffineSection (.of k) _ 0
    rw [Category.assoc, nativeAffineSection_naturality, ← Category.assoc, ih, Category.assoc]

/-- The zero maps of the two powers form a pullback over the given base map. -/
theorem affineCylinderPowerZero_isPullback {X Y : Sm(k)} (f : X ⟶ Y) (n : ℕ) :
    IsPullback (affineCylinderPowerZero k X n).left f.left
      (affineCylinderPowerMap k f n).left (affineCylinderPowerZero k Y n).left := by
  induction n with
  | zero => exact IsPullback.of_id_fst
  | succ n ih =>
    let U := affineCylinderPower k X n
    let V := affineCylinderPower k Y n
    let g := affineCylinderPowerMap k f n
    let R := CommRingCat.of k
    have h : IsPullback (nativeAffineSection R U 0).left g.left
        (affineLineCylinder.map g).left (nativeAffineSection R V 0).left := by
      let π := projection (SmoothSite.additiveGroupObject (Spec R))
      apply IsPullback.of_right (h₁₂ := (π.app U).left) (h₂₂ := (π.app V).left)
      · rw [show (nativeAffineSection R U 0).left ≫ (π.app U).left = 𝟙 _ from
            congrArg (fun h => h.left) (nativeAffineSection_projection R U 0),
          show (nativeAffineSection R V 0).left ≫ (π.app V).left = 𝟙 _ from
            congrArg (fun h => h.left) (nativeAffineSection_projection R V 0)]
        exact IsPullback.of_id_fst
      · exact congrArg (fun h => h.left) (nativeAffineSection_naturality R g 0)
      · exact (affineLineCylinder_map_isPullback g).flip
    exact ih.paste_horiz h

end AlgebraicGeometry.MotivicHomotopy
