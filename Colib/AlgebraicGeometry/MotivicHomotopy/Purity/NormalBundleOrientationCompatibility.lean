/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.NormalBundleChartCover
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.NormalBundleOrientationTransitions
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineFrameOrientation
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.NormalBundleOrientationLocal

/-!
# Compatibility of the supported normal chart classes

The normalized chart class agrees under change of frame and under restriction.
On intersections these comparisons identify the two chosen chart classes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

private theorem map_comp_eq_of_square {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B B' C₀ : C} {a : A ⟶ B} {b : B ⟶ C₀} {c : A ⟶ B'} {d : B' ⟶ C₀}
    {K : D} (τ : F.obj C₀ ⟶ K) (τ' : F.obj B' ⟶ K)
    (h : a ≫ b = c ≫ d) (hd : F.map d ≫ τ = τ') :
    F.map a ≫ F.map b ≫ τ = F.map c ≫ τ' := by
  rw [← F.map_comp_assoc, h, F.map_comp, Category.assoc, hd]

variable (k : Type u) [Field k]

local notation "Φ" => effectivePairMotiveFunctor k

variable {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X) [IsClosedImmersion i.left]
  {n m : ℕ} (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)

local notation "E₀" => (Stacks.Conormal.conormalSheafDegreeOne i.left : Z.left.Modules)
local notation "p" => normalBundleProjection i hX hZ
local notation "z" => normalBundleZeroSection i hX hZ
set_option quotPrecheck false in
local notation "jₙ" => closedPairOpenInclusion (z).left

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The canonical abelian structure on sheaves with transfers. -/
local instance normalBundleOrientationCompatibilityAbelian :
    Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable
  normalBundleBasisArrowIso

local notation "Q" => relativeOpenRestrictionMotive k (p) jₙ

section ChartMotive

variable (V : Z.left.affineOpens)

set_option quotPrecheck false in
local notation "U" => (opensFunctor Z).obj V.1

set_option maxHeartbeats 850000 in
-- The ambient chart and its frame action use the actual relative spectrum.
/-- A normalized class on an integral affine chart is independent of the basis chosen there. -/
theorem normalBundleBasisThomClass_eq
    (b : Module.Basis (Fin (n - m)) Γ(Z.left, V.1) Γ(E₀, V.1))
    [IsIntegral (U).left]
    (b' : Module.Basis (Fin (n - m)) Γ(Z.left, V.1) Γ(E₀, V.1)) :
    normalBundleBasisThomClass k i hX hZ V b =
      normalBundleBasisThomClass k i hX hZ V b' := by
  let : IsAffine (U).left := V.2
  let A := Scheme.Modules.vectorBundleFrameChangeMatrix E₀ V b b'
  let α := affineSpaceMatrixSupportArrowMap U (n - m) A
  let q := normalBundleBasisArrowIso k i hX hZ V b
  let q' := normalBundleBasisArrowIso k i hX hZ V b'
  let c := effectiveAffineSpaceThomClass k U (n - m)
  have he : q.hom ≫ α = q'.hom := normalBundleBasisArrowIso_frameChange k i hX hZ V b b'
  have ha : (Φ).map α ≫ c = c := effectiveAffineSpaceThomClass_matrixMap k U (n - m) A
  have h₀ : normalBundleBasisThomClass k i hX hZ V b = (Φ).map q.hom ≫ c :=
    normalBundleBasisThomClass_eq_map k i hX hZ V b
  have h₁ : normalBundleBasisThomClass k i hX hZ V b' = (Φ).map q'.hom ≫ c :=
    normalBundleBasisThomClass_eq_map k i hX hZ V b'
  have hmap : (Φ).map q.hom ≫ (Φ).map α = (Φ).map q'.hom :=
    ((Φ).map_comp q.hom α).symm.trans ((Φ).congr_map he)
  have h₂ : (Φ).map q'.hom ≫ c = (Φ).map q.hom ≫ c :=
    (congrArg (· ≫ c) hmap.symm).trans
      ((Category.assoc _ _ _).trans (congrArg ((Φ).map q.hom ≫ ·) ha))
  exact h₀.trans (h₂.symm.trans h₁.symm)

set_option maxHeartbeats 1000000 in
-- Identify the original restricted chart on the actual scheme before applying motives.
/-- The local normal class restricts to the class of the restricted original basis. -/
theorem normalBundleBasisThomClass_restrict
    (b : Module.Basis (Fin (n - m)) Γ(Z.left, V.1) Γ(E₀, V.1))
    (W : Z.left.affineOpens) (h : W.1 ≤ V.1) :
    (Q).map (homOfLE h) ≫ normalBundleBasisThomClass k i hX hZ V b =
      normalBundleBasisThomClass k i hX hZ W (Scheme.Modules.vectorBundleBasisRestrict E₀ b h) := by
  let U' := (opensFunctor Z).obj W.1
  let f : U' ⟶ U := (opensFunctor Z).map (homOfLE h)
  let : IsAffine U'.left := W.2
  let : IsAffine (U).left := V.2
  let b₁ := Scheme.Modules.vectorBundleBasisRestrict E₀ b h
  let α := (relativeOpenRestrictionPair k (p) jₙ).map (homOfLE h)
  let β := closedSupportArrowMap
    (i := relativeAffineSpaceZeroSection U' (n - m)) (j := relativeAffineSpaceZeroSection U (n - m))
    (f := affineSpaceObjectMap f (n - m)) (g := f) (affineSpaceOrigin_isPullback f (n - m))
  let q₀ := normalBundleBasisArrowIso k i hX hZ W b₁
  let q₁ := normalBundleBasisArrowIso k i hX hZ V b
  let c₀ := effectiveAffineSpaceThomClass k U' (n - m)
  let c₁ := effectiveAffineSpaceThomClass k U (n - m)
  have he : α ≫ q₁.hom = q₀.hom ≫ β := normalBundleBasisArrowIso_restrict k i hX hZ V b W h
  have ht : (Φ).map β ≫ c₁ = c₀ := effectiveAffineSpaceThomClass_naturality k f (n - m)
  have h₁ : normalBundleBasisThomClass k i hX hZ V b = (Φ).map q₁.hom ≫ c₁ :=
    normalBundleBasisThomClass_eq_map k i hX hZ V b
  have h₀ : normalBundleBasisThomClass k i hX hZ W b₁ = (Φ).map q₀.hom ≫ c₀ :=
    normalBundleBasisThomClass_eq_map k i hX hZ W b₁
  have hc : (Φ).map α ≫ (Φ).map q₁.hom ≫ c₁ = (Φ).map q₀.hom ≫ c₀ :=
    map_comp_eq_of_square (Φ) c₁ c₀ he ht
  exact (congrArg ((Φ).map α ≫ ·) h₁).trans (hc.trans h₀.symm)

end ChartMotive

variable {J : Type*} (V : J → Z.left.affineOpens)

/-- On the affine intersection the two original restrictions agree, by invariance under the
actual transition matrix between the two restricted bases. -/
theorem normalBundleBasisThomClass_agree
    (b : ∀ x, Module.Basis (Fin (n - m)) Γ(Z.left, (V x).1) Γ(E₀, (V x).1)) (x y : J)
    (hi : IsIntegral (V x).1.toScheme) :
    (Q).map (homOfLE (inf_le_left :
        (V x).1 ⊓ (V y).1 ≤ (V x).1)) ≫ normalBundleBasisThomClass k i hX hZ (V x) (b x) =
      (Q).map (homOfLE (inf_le_right :
        (V x).1 ⊓ (V y).1 ≤ (V y).1)) ≫ normalBundleBasisThomClass k i hX hZ (V y) (b y) := by
  classical
  let W : Z.left.affineOpens :=
    ⟨(V x).1 ⊓ (V y).1, isAffineOpen_smooth_intersection k (V x) (V y)⟩
  let h₀ : W.1 ≤ (V x).1 := inf_le_left
  let h₁ : W.1 ≤ (V y).1 := inf_le_right
  rw [normalBundleBasisThomClass_restrict k i hX hZ (V x) (b x) W h₀,
    normalBundleBasisThomClass_restrict k i hX hZ (V y) (b y) W h₁]
  by_cases hn : Nonempty W.1.toScheme
  · let : Nonempty ((opensFunctor Z).obj W.1).left := hn
    let : IsIntegral (V x).1.toScheme := hi
    let : IsIntegral ((opensFunctor Z).obj W.1).left :=
      isIntegral_of_isOpenImmersion (Z.left.homOfLE h₀)
    exact normalBundleBasisThomClass_eq k i hX hZ W _ _
  · have hb : W.1 = ⊥ := by
      apply bot_unique
      intro t ht
      exact False.elim (hn ⟨⟨t, ht⟩⟩)
    have hz : IsZero ((Q).obj W.1) := hb.symm ▸ isZero_relativeOpenRestrictionMotive_bot k (p) jₙ
    exact hz.eq_of_src _ _

end AlgebraicGeometry.MotivicHomotopy
