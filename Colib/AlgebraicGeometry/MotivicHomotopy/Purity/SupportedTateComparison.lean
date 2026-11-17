/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.LefschetzPower
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineThomGraph
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ThomDescent
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ThomGraph
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.NormalBundleOrientation
public import Colib.CategoryTheory.Triangulated.Stabilization.Stages

/-! # Identifying the normal-bundle Thom motive with its Lefschetz twist -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme
open SmoothSite Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]

attribute [local instance] thomGraphBasicCorSheafify thomGraphBasicSmoothSheafify

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S
local notation "E" => EffectiveMotivesMinus k
local notation "B" => base S
local notation "M" => effectiveSmoothMotive k
local notation "Φ" => effectivePairMotiveFunctor k
local notation "L" => effectiveLefschetzTwistFunctor k

attribute [local instance] thomGraphBasicBaseNoetherian thomGraphBasicAbelian thomGraphBasicMonoidal

attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable
  effectivePairThomGraph effectiveRestrictedThomGraph normalBundleOfSmooth normalBundleProjection

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

set_option Elab.async false in
set_option maxHeartbeats 600000 in
-- Retain the actual effective tensor iterate and smooth base motive.
/-- The coefficient of the normalized Thom class. -/
def effectiveThomCoefficient (c : ℕ) : EffectiveMotivesMinus.{u, w'} k :=
  (Stabilization.iterate (effectiveLefschetzTwistFunctor k) c).obj
    ((effectiveSmoothMotive.{u, w'} k).obj (SmoothSite.base (Spec (CommRingCat.of k))))

set_option Elab.async false in
set_option maxHeartbeats 600000 in
-- Fix the source and coefficient of the chosen class explicitly.
/-- The normalized class at the original complement pair. -/
def normalBundleThomClassAsPair
    {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i.left] {n m : ℕ}
    (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m) :
    effectivePairMotive.{u, w, w'} k
        (closedPairOpenInclusion (normalBundleZeroSection i hX hZ).left) ⟶
      effectiveThomCoefficient k (n - m) :=
  let c := normalBundleThomClass.{u, w, w', w''} k i hX hZ
  c

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option Elab.async false in
set_option maxHeartbeats 1400000 in
-- Use the composition of the original restriction with the class at the affine endpoint.
/-- The supported graph map is invertible on each chart on which its class has the original
normalized affine-space value. -/
theorem isIso_effectiveRestrictedThomGraph_of_basis
    {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i.left] {n m : ℕ}
    (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)
    (W : Z.left.affineOpens)
    (b : Module.Basis (Fin (n - m)) Γ(Z.left, (W.1 : Z.left.Opens))
      Γ((Stacks.Conormal.conormalSheafDegreeOne i.left : Z.left.Modules), (W.1 : Z.left.Opens)))
    (t : effectivePairMotive k (closedPairOpenInclusion (normalBundleZeroSection i hX hZ).left) ⟶
      (effectiveThomCoefficient k (n - m)))
    (ht :
      let p : normalBundleOfSmooth i ⟶ Z := normalBundleProjection i hX hZ
      let j := closedPairOpenInclusion (normalBundleZeroSection i hX hZ).left
      let P : Z.left.Opens ⥤ E := relativeOpenRestrictionMotive k p j
      let r : P.obj W.1 ⟶ P.obj (⊤ : Z.left.Opens) := P.map (homOfLE (le_top : W.1 ≤ ⊤))
      let e : P.obj (⊤ : Z.left.Opens) ⟶ effectivePairMotive k j :=
        (relativeOpenRestrictionTopIso k p j).hom
      let c : P.obj W.1 ⟶ effectiveThomCoefficient k (n - m) :=
        normalBundleBasisThomClass.{u, w, w', w''} k i hX hZ W b
      r ≫ e ≫ t = c) :
    IsIso (effectiveRestrictedThomGraph k (normalBundleProjection i hX hZ)
      (closedPairOpenInclusion (normalBundleZeroSection i hX hZ).left) W.1 t) := by
  let p : normalBundleOfSmooth i ⟶ Z := normalBundleProjection i hX hZ
  let j := closedPairOpenInclusion (normalBundleZeroSection i hX hZ).left
  let P : Z.left.Opens ⥤ E := relativeOpenRestrictionMotive k p j
  let Y := (opensFunctor Z).obj W.1
  let : IsAffine Y.left := W.2
  let a := normalBundleBasisArrowIso k i hX hZ W b
  let q := preimageOpenMap Z p W.1
  let j₀ := preimageOpenMap (normalBundleOfSmooth i) j (p.left ⁻¹ᵁ W.1)
  let p' := affineSpaceProjection Y (n - m)
  let j' := closedPairOpenInclusion (relativeAffineSpaceZeroSection Y (n - m)).left
  let c := effectiveAffineSpaceThomClass k Y (n - m)
  let m₀ : effectivePairMotive k j₀ ⟶ effectivePairMotive k j' := (Φ).map a.hom
  let r : P.obj W.1 ⟶ P.obj (⊤ : Z.left.Opens) := P.map (homOfLE (le_top : W.1 ≤ ⊤))
  let d : P.obj (⊤ : Z.left.Opens) ⟶ effectivePairMotive k j :=
    (relativeOpenRestrictionTopIso k p j).hom
  have he : a.hom.right ≫ p' = q :=
    (congrArg (· ≫ p') (normalBundleBasisArrowIso_hom_right k i hX hZ W b)).trans
      (normalBundleBasisChart_projection i hX hZ W b)
  let cW : P.obj W.1 ⟶ effectiveThomCoefficient k (n - m) :=
    normalBundleBasisThomClass.{u, w, w', w''} k i hX hZ W b
  have hc : cW = m₀ ≫ c :=
    normalBundleBasisThomClass_eq_map k i hX hZ W b
  let K := effectiveThomCoefficient k (n - m)
  let g := effectivePairThomGraph k (Y := Y) (j := j₀) q (K := K)
  let g' := effectivePairThomGraph k (Y := Y) (j := j') p' (K := K) c
  have hclass : (r ≫ d) ≫ t = m₀ ≫ c :=
    (Category.assoc r d t).trans (ht.trans hc)
  have hrestrict : effectiveRestrictedThomGraph k p j W.1 t = g ((r ≫ d) ≫ t) :=
    effectiveRestrictedThomGraph_eq_restrict k p j W.1 t
  have hgraph : m₀ ≫ g' = g (m₀ ≫ c) :=
    effectivePairThomGraph_naturality k a.hom q p' he c
  let : IsIso g' := isIso_effectiveAffineSpaceThomGraph k Y (n - m)
  exact (congrArg IsIso (hrestrict.trans ((congrArg g hclass).trans hgraph.symm))).mpr
    (inferInstance : IsIso (m₀ ≫ g'))

set_option Elab.async false in
set_option maxHeartbeats 900000 in
-- Use the original projection and fixed normalized class in the graph.
/-- The whole normal-bundle graph with its chosen class. -/
def effectiveNormalBundleThomGraph
    {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i.left] {n m : ℕ}
    (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m) :
    effectiveMotiveWithSupport k (normalBundleZeroSection i hX hZ) ⟶
      effectiveThomCoefficient k (n - m) ⊗ (effectiveSmoothMotive.{u, w'} k).obj Z := by
  let p : normalBundleOfSmooth i ⟶ Z := normalBundleProjection i hX hZ
  let j := closedPairOpenInclusion (normalBundleZeroSection i hX hZ).left
  let K : EffectiveMotivesMinus.{u, w'} k := effectiveThomCoefficient k (n - m)
  let c : effectivePairMotive.{u, w, w'} k j ⟶ K := normalBundleThomClassAsPair k i hX hZ
  exact effectivePairThomGraph k (V := normalBundleOfSmooth i) (Y := Z) (j := j) p (K := K) c

set_option Elab.async false in
set_option maxHeartbeats 800000 in
-- Fix the restriction and graph endpoints before applying the class.
/-- The actual graph over an open of the normal-bundle base. -/
private def normalBundleRestrictedThomGraph
    {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i.left] {n m : ℕ}
    (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)
    (U : Z.left.Opens)
    (t : effectivePairMotive.{u, w, w'} k
        (closedPairOpenInclusion (normalBundleZeroSection i hX hZ).left) ⟶
      effectiveThomCoefficient k (n - m)) :
    (relativeOpenRestrictionMotive k (normalBundleProjection i hX hZ)
      (closedPairOpenInclusion (normalBundleZeroSection i hX hZ).left)).obj U ⟶
      effectiveThomCoefficient k (n - m) ⊗ (effectiveSmoothMotive.{u, w'} k).obj
        ((opensFunctor Z).obj U) :=
  effectiveRestrictedThomGraph k (normalBundleProjection i hX hZ)
    (closedPairOpenInclusion (normalBundleZeroSection i hX hZ).left) U
    (K := effectiveThomCoefficient k (n - m)) t

set_option Elab.async false in
set_option maxHeartbeats 1800000 in
-- Use the canonical class on the chosen finite cover and its actual top restriction.
/-- The chosen class gives an invertible global graph from its affine chart comparisons. -/
theorem isIso_effectiveNormalBundleThomGraph
    {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i.left] {n m : ℕ}
    (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m) :
    IsIso (effectiveNormalBundleThomGraph k i hX hZ) := by
  classical
  let p : normalBundleOfSmooth i ⟶ Z := normalBundleProjection i hX hZ
  let j := closedPairOpenInclusion (normalBundleZeroSection i hX hZ).left
  let K : EffectiveMotivesMinus.{u, w'} k := effectiveThomCoefficient k (n - m)
  let g (U : Z.left.Opens) (t : effectivePairMotive.{u, w, w'} k j ⟶ K) :=
    normalBundleRestrictedThomGraph k i hX hZ U t
  let data := exists_finset_integral_normalBundleBasisCover k i hX hZ
  let V := data.choose
  let b := data.choose_spec.choose
  let s := data.choose_spec.choose_spec.choose
  let hc := data.choose_spec.choose_spec.choose_spec.1
  let hi := data.choose_spec.choose_spec.choose_spec.2
  let hzero := fun U => normalBundleThomClass_shift_vanishing k i hX hZ V s b hc U 1 (by decide)
  let hclasses := fun x y => normalBundleBasisThomClass_agree k i hX hZ V b x y (hi x)
  let t : effectivePairMotive.{u, w, w'} k j ⟶ K := normalBundleThomClassAsPair k i hX hZ
  let t' : effectivePairMotive.{u, w, w'} k j ⟶ K :=
    normalBundleThomClassOfCharts k i hX hZ V s b hc hzero hclasses
  have ht : t = t' := normalBundleThomClass_eq_of_chosenCover k i hX hZ
  have hlocal (x : Z.left) (hx : x ∈ s) (W : Z.left.affineOpens) (hW : W.1 ≤ (V x).1) :
      IsIso (g W.1 t') := by
    let N := Stacks.Conormal.conormalSheafDegreeOne i.left
    let bW := Scheme.Modules.vectorBundleBasisRestrict N (b x) hW
    exact isIso_effectiveRestrictedThomGraph_of_basis k i hX hZ W bW t'
      (normalBundleThomClassOfCharts_restrict_subopen k i hX hZ V s b hc hzero hclasses x hx W hW)
  have hTop' : IsIso (g ⊤ t') :=
    isIso_effectiveRestrictedThomGraph_of_cover k p j t' s V hc hlocal
  let : IsIso (g ⊤ t) := (congrArg (fun τ => IsIso (g ⊤ τ)) ht).mpr hTop'
  let e := relativeOpenRestrictionTopIso k p j
  let f := effectiveNormalBundleThomGraph k i hX hZ
  let h := (tensorLeft K).mapIso ((M).mapIso (smoothTopOpenIso k Z))
  have hcomp : g ⊤ t ≫ h.hom = e.hom ≫ f := effectiveRestrictedThomGraph_top k p j t
  exact IsIso.of_isIso_fac_left (f := e.hom) (g := f) (h := g ⊤ t ≫ h.hom) hcomp.symm

set_option Elab.async false in
set_option maxHeartbeats 900000 in
-- Compose the actual supported graph with the canonical Lefschetz power comparison.
/-- The normal-bundle Thom isomorphism in the original integral effective category. -/
def effectiveNormalBundleThomIso
    {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i.left] {n m : ℕ}
    (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m) :
    effectiveMotiveWithSupport k (normalBundleZeroSection i hX hZ) ≅
      (Stabilization.iterate (effectiveLefschetzTwistFunctor k) (n - m)).obj
        ((effectiveSmoothMotive.{u, w'} k).obj Z) := by
  let g := effectiveNormalBundleThomGraph k i hX hZ
  let MZ := (effectiveSmoothMotive.{u, w'} k).obj Z
  letI : IsIso g := isIso_effectiveNormalBundleThomGraph k i hX hZ
  exact asIso g ≪≫ effectiveLefschetzPowerTensorIso k MZ (n - m)

end AlgebraicGeometry.MotivicHomotopy
