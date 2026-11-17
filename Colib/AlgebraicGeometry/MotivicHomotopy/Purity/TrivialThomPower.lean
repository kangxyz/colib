/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.RelativeLineNaturality
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.TrivialThomPowerNaturality

/-! # Naturality of the supported Thom motives of trivial affine bundles -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k]

set_option quotPrecheck false in
local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]

/-- The native abelian structure on transfer sheaves for the iterated line pair comparison. -/
local instance instAbelianTrivialThomPower : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

local instance instNoetherianTrivialThomPower :
    IsNoetherian (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
  inferInstanceAs (IsNoetherian (Spec (CommRingCat.of k)))

attribute [local irreducible] Cor.graphFunctor transferRepresentable

variable [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]

local notation "L" => effectiveLefschetzTwistFunctor k
local notation "P" => effectivePairMotiveFunctor k

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1200000 in
-- Assemble naturality with the actual maps of the marked cylinder towers.
/-- The normalized comparison for a trivial bundle commutes with the original
maps of the base scheme. -/
theorem effectiveTrivialPowerThomIso_naturality {X Y : Sm} (f : X ⟶ Y) (n : ℕ) :
    let q := fun d => closedSupportArrowMap
      (i := affineCylinderPowerZero k X d) (j := affineCylinderPowerZero k Y d)
      (f := affineCylinderPowerMap k f d) (g := f) (affineCylinderPowerZero_isPullback k f d)
    (P).map (q n) ≫ (effectiveTrivialPowerThomIso k Y n).hom =
      (effectiveTrivialPowerThomIso k X n).hom ≫
        (Stabilization.iterate (L) n).map ((effectiveSmoothMotive k).map f) := by
  intro q
  have hs (d : ℕ) :
      (P).map (q (d + 1)) ≫ (effectiveAppendZeroSectionThomIso k
        (affineCylinderPowerZero k Y d)).hom =
      (effectiveAppendZeroSectionThomIso k (affineCylinderPowerZero k X d)).hom ≫
        (L).map ((P).map (q d)) := by
    let R := CommRingCat.of k
    let z := affineCylinderPowerZero k X d
    let z' := affineCylinderPowerZero k Y d
    let b := affineCylinderPowerMap k f d
    let h := affineCylinderPowerZero_isPullback k f d
    let v := closedSupportArrowMap (i := z) (j := z') (f := b) (g := f) h
    let u := closedSupportArrowMap
      (i := appendZeroSection R z) (j := appendZeroSection R z')
      (f := affineLineCylinder.map b) (g := f)
      (appendZeroSection_isPullback R z (z' := z') (a := f) (b := b) h)
    let e := effectiveAppendZeroSectionThomIso k z
    let e' := effectiveAppendZeroSectionThomIso k z'
    have h₀ : q d = v := closedSupportArrowMap_eq_of_right (i := z) (j := z') rfl
    have h₁ : q (d + 1) = u :=
      closedSupportArrowMap_eq_of_right
        (i := appendZeroSection R z) (j := appendZeroSection R z') rfl
    have hₙ : (P).map u ≫ e'.hom = e.hom ≫ (L).map ((P).map v) :=
      effectiveAppendZeroSectionThomIso_naturality k z (z' := z') (a := f) (b := b) h
    exact (congrArg (· ≫ e'.hom) ((P).congr_map h₁)).trans
      (hₙ.trans (congrArg (e.hom ≫ ·) ((L).congr_map ((P).congr_map h₀.symm))))
  exact effectiveTrivialPowerThomIso_naturality_of_append k (X := X) (Y := Y) f n hs

end AlgebraicGeometry.MotivicHomotopy
