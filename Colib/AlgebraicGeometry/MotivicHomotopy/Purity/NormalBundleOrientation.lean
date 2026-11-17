/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.NormalBundleOrientationDescent

/-! # The supported Thom class on the original normal bundle -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [baseField : Field k]

local notation "Base" => Spec (CommRingCat.of k)
local notation "M" => effectiveSmoothMotive k

variable {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X)
  [closedImmersion : IsClosedImmersion i.left]
  {n m : ℕ} (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)

local notation "z" => normalBundleZeroSection i hX hZ

variable [perfectField : PerfectField k]
  [presheafDerived : HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [sheafDerived : HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [groupDerived : HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [nisnevichExt :
    HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The canonical abelian structure on sheaves with transfers. -/
local instance normalBundleOrientationAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable

local notation "L" => Stabilization.iterate (effectiveLefschetzTwistFunctor k) (n - m)
set_option quotPrecheck false in
local notation "K" => (L).obj ((M).obj (base Base))

set_option maxHeartbeats 1000000 in
-- Keep the formula at the original finite cover in the type of the witness.
private theorem exists_normalBundleThomClass :
    let h := exists_finset_integral_normalBundleBasisCover k i hX hZ
    let V := h.choose
    let b := h.choose_spec.choose
    let ts := h.choose_spec.choose_spec.choose
    let hc := h.choose_spec.choose_spec.choose_spec.1
    let hi := h.choose_spec.choose_spec.choose_spec.2
    ∃ t : effectiveMotiveWithSupport k (z) ⟶ K,
      t = normalBundleThomClassOfCharts k i hX hZ V ts b hc
      (fun U : Z.left.Opens => normalBundleThomClass_shift_vanishing k i hX hZ V ts b hc U 1
        (by decide))
      (fun x y => normalBundleBasisThomClass_agree k i hX hZ V b x y (hi x)) :=
  exists_eq

/-- The actual supported Thom class of the normal bundle, normalized on its affine charts. -/
@[no_expose]
def normalBundleThomClass : effectiveMotiveWithSupport k (z) ⟶ K :=
  (exists_normalBundleThomClass k i hX hZ).choose

set_option maxHeartbeats 1000000 in
-- Use the exact formula without reducing the chosen map in the graph comparison.
/-- The global Thom class is the normalized class of the chosen finite affine basis cover. -/
theorem normalBundleThomClass_eq_of_chosenCover :
    let h := exists_finset_integral_normalBundleBasisCover k i hX hZ
    let V := h.choose
    let b := h.choose_spec.choose
    let ts := h.choose_spec.choose_spec.choose
    let hc := h.choose_spec.choose_spec.choose_spec.1
    let hi := h.choose_spec.choose_spec.choose_spec.2
    normalBundleThomClass k i hX hZ = normalBundleThomClassOfCharts k i hX hZ V ts b hc
      (fun U : Z.left.Opens => normalBundleThomClass_shift_vanishing k i hX hZ V ts b hc U 1
        (by decide))
      (fun x y => normalBundleBasisThomClass_agree k i hX hZ V b x y (hi x)) :=
  (exists_normalBundleThomClass k i hX hZ).choose_spec

end AlgebraicGeometry.MotivicHomotopy
