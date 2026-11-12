/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.SourceChangedMatching
public import Colib.AlgebraicGeometry.Divisors.FrameTransport
public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.TensorPowerTensor
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeProperties
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeUnits
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic

/-!
# Coefficients of the original normalized section pairs

On an actual chart where the numerator generates, the graph-times-denominator
section has a coefficient in that frame. Where the denominator also generates,
this coefficient cuts out the original graph. Its boundary value is the
original graph coordinate prescribed in the normalization.

Adapted from
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Boundary/SectionPairNormIdeal.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Stacks.Ample Stacks.Divisors
open Stacks.SheafOfModules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

variable {X : Scheme.{u}}

local instance (L : X.Modules) [hL : IsInvertibleModule X L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := hL

local instance (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] :
    IsInvertibleModule X (divisorSheaf D) := Stacks.Divisors.isInvertible_divisorSheaf D

/-- Once a section generates on one chart, it generates through every
specified factorization through that same chart. -/
theorem zeroScheme_pullback_eq_top_of_factor {Y Z : Scheme.{u}}
    (g : Y ⟶ X) (g' : Z ⟶ X) (v : Z ⟶ Y) (h : v ≫ g = g')
    (L : X.Modules) [IsInvertibleModule X L] (a : Γ(L, ⊤))
    (ha : zeroScheme Y ((Modules.pullback g).obj L) (pullbackGlobalSections g L a) = ⊤) :
    zeroScheme Z ((Modules.pullback g').obj L) (pullbackGlobalSections g' L a) = ⊤ := by
  apply (Stacks.Divisors.zeroScheme_pullback g' L a).trans
  rw [← h, IdealSheafData.comap_comp]
  exact (congrArg (fun I : Y.IdealSheafData ↦ I.comap v)
    ((Stacks.Divisors.zeroScheme_pullback g L a).symm.trans ha)).trans
      (IdealSheafData.comap_top v)

/-- The coefficient of a section in the frame given by a generating section. -/
def sectionRatioCoefficient (L : X.Modules) [IsInvertibleModule X L]
    (a b : Γ(L, ⊤)) (ha : zeroScheme X L a = ⊤) : Γ(X, ⊤) :=
  (frameOfZeroSchemeTop L a ha).hom.app ⊤ b

/-- The exact coefficient expresses the original section in the specified frame. -/
theorem sectionRatioCoefficient_smul_eq (L : X.Modules) [IsInvertibleModule X L]
    (a b : Γ(L, ⊤)) (ha : zeroScheme X L a = ⊤) :
    sectionRatioCoefficient L a b ha • a = b := by
  let e := frameOfZeroSchemeTop L a ha
  let c : Γ(X, ⊤) := e.hom.app ⊤ b
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective
  have he : e.hom.app ⊤ a = (1 : Γ(X, ⊤)) := frameOfZeroSchemeTop_section L a ha
  change e.hom.app ⊤ (c • a) = e.hom.app ⊤ b
  rw [Modules.Hom.app_smul, he]
  change c * 1 = c
  exact mul_one c

/-- Changing the source of the same generating section keeps its unit ideal. -/
theorem zeroScheme_pullbackSquare_eq_top {X' W W' : Scheme.{u}}
    (g : X' ⟶ X) (i : W ⟶ X) (i' : W' ⟶ X') (β : W' ⟶ W) (h : i' ≫ g = β ≫ i)
    (L : X.Modules) [IsInvertibleModule X L] (a : Γ(L, ⊤))
    (ha : zeroScheme W ((Modules.pullback i).obj L) (pullbackGlobalSections i L a) = ⊤) :
    zeroScheme W' ((Modules.pullback i').obj ((Modules.pullback g).obj L))
      (pullbackGlobalSections i' _ (pullbackGlobalSections g L a)) = ⊤ := by
  apply (Stacks.Divisors.zeroScheme_pullback i' ((Modules.pullback g).obj L)
    (pullbackGlobalSections g L a)).trans
  have hg := congrArg (fun I : X'.IdealSheafData ↦ I.comap i')
    (Stacks.Divisors.zeroScheme_pullback g L a)
  refine hg.trans ?_
  rw [← IdealSheafData.comap_comp, h, IdealSheafData.comap_comp]
  exact (congrArg (fun I : W.IdealSheafData ↦ I.comap β)
    ((Stacks.Divisors.zeroScheme_pullback i L a).symm.trans ha)).trans
      (IdealSheafData.comap_top β)

/-- The ratio of the same two sections restricts along the actual scalar map
in a commutative source-change square. -/
theorem sectionRatioCoefficient_appTop_of_pullbackSquare {X' W W' : Scheme.{u}}
    (g : X' ⟶ X) (i : W ⟶ X) (i' : W' ⟶ X') (β : W' ⟶ W) (h : i' ≫ g = β ≫ i)
    (L : X.Modules) [IsInvertibleModule X L] (a b : Γ(L, ⊤))
    (ha : zeroScheme W ((Modules.pullback i).obj L) (pullbackGlobalSections i L a) = ⊤)
    (ha' : zeroScheme W' ((Modules.pullback i').obj ((Modules.pullback g).obj L))
      (pullbackGlobalSections i' _ (pullbackGlobalSections g L a)) = ⊤) :
    β.appTop (sectionRatioCoefficient _ (pullbackGlobalSections i L a)
      (pullbackGlobalSections i L b) ha) =
    sectionRatioCoefficient _ (pullbackGlobalSections i' _ (pullbackGlobalSections g L a))
      (pullbackGlobalSections i' _ (pullbackGlobalSections g L b)) ha' := by
  let a' := pullbackGlobalSections i' _ (pullbackGlobalSections g L a)
  let b' := pullbackGlobalSections i' _ (pullbackGlobalSections g L b)
  let c := sectionRatioCoefficient _ (pullbackGlobalSections i L a)
    (pullbackGlobalSections i L b) ha
  have hc : pullbackGlobalSections i L b = c • pullbackGlobalSections i L a :=
    (sectionRatioCoefficient_smul_eq _ _ _ ha).symm
  have hab : b' = β.appTop c • a' :=
    boundary_smul_identity_after_sourceChange g i i' β h L b a c hc
  let e := frameOfZeroSchemeTop _ a' ha'
  have he : e.hom.app ⊤ a' = (1 : Γ(W', ⊤)) := frameOfZeroSchemeTop_section _ _ _
  change β.appTop c = e.hom.app ⊤ b'
  rw [hab, Modules.Hom.app_smul, he]
  exact (mul_one (β.appTop c)).symm

/-- The coefficient in an affine frame generates the actual zero ideal. -/
theorem zeroScheme_ideal_eq_span_frame [IsAffine X]
    (L : X.Modules) [IsInvertibleModule X L]
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) (b : Γ(L, ⊤)) :
    (zeroScheme X L b).ideal ⟨⊤, isAffineOpen_top X⟩ =
      Ideal.span ({e.hom.app ⊤ b} : Set Γ(X, ⊤)) := by
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let b₀ : Γ(X, ⊤) := e.hom.app ⊤ b
  have he : zeroScheme X (SheafOfModules.unit X.ringCatSheaf) b₀ = zeroScheme X L b :=
    zeroScheme_congr_iso e b
  calc
    _ = (zeroScheme X (SheafOfModules.unit X.ringCatSheaf) b₀).ideal U :=
      congrArg (fun I : X.IdealSheafData ↦ I.ideal U) he.symm
    _ = _ := zeroScheme_ideal_of_trivialization X (SheafOfModules.unit X.ringCatSheaf)
      b₀ U (LinearEquiv.refl (Γ(X, ⊤)) (Γ(X, ⊤))) b₀ (by
        simp [U]
        rfl)

/-- On an affine chart the coefficient generates the exact zero ideal. -/
theorem zeroScheme_ideal_eq_span_sectionRatioCoefficient [IsAffine X]
    (L : X.Modules) [IsInvertibleModule X L]
    (a b : Γ(L, ⊤)) (ha : zeroScheme X L a = ⊤) :
    (zeroScheme X L b).ideal ⟨⊤, isAffineOpen_top X⟩ =
      Ideal.span {sectionRatioCoefficient L a b ha} :=
  zeroScheme_ideal_eq_span_frame L (frameOfZeroSchemeTop L a ha) b

/-- A scalar equation after restriction identifies the literal restriction of the
coefficient. -/
theorem appTop_sectionRatioCoefficient_of_smul {Z : Scheme.{u}} (i : Z ⟶ X)
    (L : X.Modules) [IsInvertibleModule X L]
    (a b : Γ(L, ⊤)) (ha : zeroScheme X L a = ⊤) (r : Γ(Z, ⊤))
    (h : pullbackGlobalSections i L b = r • pullbackGlobalSections i L a) :
    i.appTop (sectionRatioCoefficient L a b ha) = r := by
  rw [sectionRatioCoefficient, ← Modules.framePullback_coordinate, h,
    Modules.Hom.app_smul, Modules.framePullback_coordinate, frameOfZeroSchemeTop_section,
    map_one, smul_eq_mul, mul_one]

variable {W : Scheme.{u}} (g : W ⟶ X)
  (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
  (T : X.Modules) [IsInvertibleModule X T]

local notation "L" => (Stacks.Divisors.tensorModules (divisorSheaf D) T)
local notation "graphPole" =>
  (tensorSection (divisorSheaf D) T ⊤ (divisorSheafGlobalSection D))

/-- The original graph-times-denominator coordinate on a chart where the
original numerator generates. -/
def graphSectionRatioCoefficient (a : Γ(L, ⊤)) (b : Γ(T, ⊤))
    (ha : zeroScheme W ((Modules.pullback g).obj L) (pullbackGlobalSections g L a) = ⊤) :
    Γ(W, ⊤) :=
  sectionRatioCoefficient ((Modules.pullback g).obj L) (pullbackGlobalSections g L a)
    (pullbackGlobalSections g L (graphPole b)) ha

/-- Reading the original two sections in any other chart frame recovers the
same ratio by an actual multiplication equation. -/
theorem graphSectionRatioCoefficient_mul_frameCoordinate
    (e : (Modules.pullback g).obj L ≅ SheafOfModules.unit W.ringCatSheaf)
    (a : Γ(L, ⊤)) (b : Γ(T, ⊤))
    (ha : zeroScheme W ((Modules.pullback g).obj L) (pullbackGlobalSections g L a) = ⊤) :
    let a₀ : Γ(W, ⊤) := e.hom.app ⊤ (pullbackGlobalSections g L a)
    let b₀ : Γ(W, ⊤) := e.hom.app ⊤ (pullbackGlobalSections g L (graphPole b))
    graphSectionRatioCoefficient g D T a b ha * a₀ = b₀ := by
  have h := congrArg (fun s ↦ e.hom.app ⊤ s)
    (sectionRatioCoefficient_smul_eq ((Modules.pullback g).obj L)
      (pullbackGlobalSections g L a) (pullbackGlobalSections g L (graphPole b)) ha)
  rw [Modules.Hom.app_smul] at h
  exact h

omit [IsEffectiveCartierDivisor D] [IsInvertibleModule X T] in
/-- The exact frame on a composed chart restricts both of its original
section coordinates along the literal ring map. -/
theorem pullbackComp_frameCoordinate {Q : Scheme.{u}} (v : Q ⟶ W)
    (e : (Modules.pullback g).obj L ≅ SheafOfModules.unit W.ringCatSheaf)
    (s : Γ(L, ⊤)) :
    (((Modules.pullbackComp v g).app L).symm ≪≫ Modules.framePullback v e).hom.app ⊤
      (pullbackGlobalSections (v ≫ g) L s) =
      v.appTop (e.hom.app ⊤ (pullbackGlobalSections g L s)) := by
  let d := (Modules.pullbackComp v g).app L
  let x : Γ((Modules.pullback v).obj ((Modules.pullback g).obj L), ⊤) :=
    pullbackGlobalSections v ((Modules.pullback g).obj L) (pullbackGlobalSections g L s)
  have h : d.hom.app ⊤ x = pullbackGlobalSections (v ≫ g) L s :=
    SectionsEqualizer.pullbackGlobalSections_comp v g L s
  have hd : d.inv.app ⊤ (d.hom.app ⊤ x) = x := congrArg (fun k ↦ k.app ⊤ x) d.hom_inv_id
  change (Modules.framePullback v e).hom.app ⊤
    (d.inv.app ⊤ (pullbackGlobalSections (v ≫ g) L s)) = _
  calc
    _ = (Modules.framePullback v e).hom.app ⊤ (d.inv.app ⊤ (d.hom.app ⊤ x)) :=
      congrArg (fun t ↦ (Modules.framePullback v e).hom.app ⊤ (d.inv.app ⊤ t)) h.symm
    _ = (Modules.framePullback v e).hom.app ⊤ x := congrArg _ hd
    _ = _ := Modules.framePullback_coordinate v e (pullbackGlobalSections g L s)

/-- Changing the actual chart pulls back the same graph coefficient. -/
theorem graphSectionRatioCoefficient_comp {Q : Scheme.{u}} (v : Q ⟶ W)
    (a : Γ(L, ⊤)) (b : Γ(T, ⊤))
    (ha : zeroScheme W ((Modules.pullback g).obj L) (pullbackGlobalSections g L a) = ⊤)
    (ha' : zeroScheme Q ((Modules.pullback (v ≫ g)).obj L)
      (pullbackGlobalSections (v ≫ g) L a) = ⊤) :
    v.appTop (graphSectionRatioCoefficient g D T a b ha) =
      graphSectionRatioCoefficient (v ≫ g) D T a b ha' := by
  let M := (Modules.pullback g).obj L
  let e := (Modules.pullbackComp v g).app L
  have h : graphSectionRatioCoefficient g D T a b ha • pullbackGlobalSections g L a =
      pullbackGlobalSections g L (graphPole b) :=
    sectionRatioCoefficient_smul_eq M _ _ ha
  have hv := congrArg (fun x : Γ(M, ⊤) ↦ e.hom.app ⊤ (pullbackGlobalSections v M x)) h
  have hComp (x : Γ(L, ⊤)) :
      e.hom.app ⊤ (pullbackGlobalSections v M (pullbackGlobalSections g L x)) =
        pullbackGlobalSections (v ≫ g) L x :=
    SectionsEqualizer.pullbackGlobalSections_comp v g L x
  rw [SectionsEqualizer.pullbackGlobalSections_smul, Modules.Hom.app_smul,
    hComp a, hComp (graphPole b)] at hv
  let E := frameOfZeroSchemeTop ((Modules.pullback (v ≫ g)).obj L)
    (pullbackGlobalSections (v ≫ g) L a) ha'
  have hGen : E.hom.app ⊤ (pullbackGlobalSections (v ≫ g) L a) = (1 : Γ(Q, ⊤)) :=
    frameOfZeroSchemeTop_section _ _ _
  have hE := congrArg (fun x ↦ E.hom.app ⊤ x) hv
  rw [Modules.Hom.app_smul, hGen] at hE
  change v.appTop (graphSectionRatioCoefficient g D T a b ha) * 1 =
    graphSectionRatioCoefficient (v ≫ g) D T a b ha' at hE
  simpa only [mul_one] using hE

/-- The graph-times-denominator section cuts out the original graph wherever
the denominator is a generator. -/
theorem zeroScheme_pullback_graphPole_eq_comap (b : Γ(T, ⊤))
    (hb : zeroScheme W ((Modules.pullback g).obj T) (pullbackGlobalSections g T b) = ⊤) :
    zeroScheme W ((Modules.pullback g).obj L) (pullbackGlobalSections g L (graphPole b)) =
      D.comap g := by
  let e : (Modules.pullback g).obj L ≅
      Stacks.Divisors.tensorModules ((Modules.pullback g).obj (divisorSheaf D))
        ((Modules.pullback g).obj T) :=
    Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g (divisorSheaf D) T
  calc
    _ = zeroScheme W _ (e.hom.app ⊤ (pullbackGlobalSections g L (graphPole b))) :=
      (zeroScheme_congr_iso e _).symm
    _ = _ := by
      have he := pullbackTensorIso_tensorSection g (divisorSheaf D) T
        (divisorSheafGlobalSection D) b
      change e.hom.app ⊤ (pullbackGlobalSections g L (graphPole b)) = _ at he
      rw [he, zeroScheme_tensorSection_eq_mul, hb, IdealSheafData.mul_top]
      exact (Stacks.Divisors.zeroScheme_pullback g _ (divisorSheafGlobalSection D)).trans
        (congrArg (fun J : X.IdealSheafData ↦ J.comap g) (zeroScheme_canonicalSection D))

/-- Where the denominator generates as well, the coefficient cuts out the whole
original graph ideal pulled back along the chart map. -/
theorem graphSectionRatioCoefficient_ideal [IsAffine W]
    (a : Γ(L, ⊤)) (b : Γ(T, ⊤))
    (ha : zeroScheme W ((Modules.pullback g).obj L) (pullbackGlobalSections g L a) = ⊤)
    (hb : zeroScheme W ((Modules.pullback g).obj T) (pullbackGlobalSections g T b) = ⊤) :
    (D.comap g).ideal ⟨⊤, isAffineOpen_top W⟩ =
      Ideal.span {graphSectionRatioCoefficient g D T a b ha} := by
  rw [← zeroScheme_pullback_graphPole_eq_comap g D T b hb]
  exact zeroScheme_ideal_eq_span_sectionRatioCoefficient _ _ _ ha

/-- The same coordinate is regular on any affine pullback where the graph
remains Cartier, including the complete marked boundary. -/
theorem isRegular_appTop_graphSectionRatioCoefficient {Q : Scheme.{u}} [IsAffine Q]
    (v : Q ⟶ W) (hD : IsEffectiveCartierDivisor ((D.comap g).comap v))
    (a : Γ(L, ⊤)) (b : Γ(T, ⊤))
    (ha : zeroScheme W ((Modules.pullback g).obj L) (pullbackGlobalSections g L a) = ⊤)
    (hb : zeroScheme W ((Modules.pullback g).obj T) (pullbackGlobalSections g T b) = ⊤) :
    _root_.IsRegular (v.appTop (graphSectionRatioCoefficient g D T a b ha)) := by
  let M := (Modules.pullback g).obj L
  let e := frameOfZeroSchemeTop M (pullbackGlobalSections g L a) ha
  have hzero :=
    (Stacks.Divisors.zeroScheme_pullback v M (pullbackGlobalSections g L (graphPole b))).trans
      (congrArg (fun J : W.IdealSheafData ↦ J.comap v)
        (zeroScheme_pullback_graphPole_eq_comap g D T b hb))
  apply isRegular_iff_mem_nonZeroDivisors.2
  apply Stacks.Divisors.Eta.mem_nonZeroDivisors_of_ideal_eq_span _ hD
    ⟨⊤, isAffineOpen_top Q⟩
  rw [← hzero, zeroScheme_ideal_eq_span_frame _ (Modules.framePullback v e),
    Modules.framePullback_coordinate]
  rfl

/-- On any literal pullback of the original boundary, the same coefficient has
the original full graph value under the specified ring map. -/
theorem graphSectionRatioCoefficient_boundary {Z Z' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ W) (β : Z' ⟶ Z) (h : i' ≫ g = β ≫ i)
    (e : (Modules.pullback i).obj (divisorSheaf D) ≅ SheafOfModules.unit Z.ringCatSheaf)
    (a : Γ(L, ⊤)) (b : Γ(T, ⊤))
    (ha : zeroScheme W ((Modules.pullback g).obj L) (pullbackGlobalSections g L a) = ⊤)
    (hn : (fixedFactorBoundaryIso i (divisorSheaf D) T e).hom.app ⊤
      (pullbackGlobalSections i L a) = pullbackGlobalSections i T b) :
    i'.appTop (graphSectionRatioCoefficient g D T a b ha) =
      β.appTop (e.hom.app ⊤
        (pullbackGlobalSections i (divisorSheaf D) (divisorSheafGlobalSection D))) := by
  apply appTop_sectionRatioCoefficient_of_smul
  exact boundary_smul_identity_after_sourceChange g i i' β h L _ _ _
    (graphPole_boundary_eq_coordinate_smul i (divisorSheaf D) T e
      (divisorSheafGlobalSection D) a b hn)

end AlgebraicGeometry.Scheme.RelativeCurvePencil
