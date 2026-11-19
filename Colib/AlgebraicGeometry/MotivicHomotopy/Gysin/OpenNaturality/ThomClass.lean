/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Gysin.OpenNaturality.ThomChart

/-! # Open restriction of the normalized normal-bundle Thom class -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme TopologicalSpace
open SmoothSite Contraction Stacks.Conormal Stacks.Deformation

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

private theorem exists_mem_finset_open_cover {T : Type*} [TopologicalSpace T] {J : Type*}
    (V : J → Opens T) (s : Finset J) (hs : s.sup V = ⊤) (z : T) :
    ∃ x ∈ s, z ∈ V x := by
  have hz : z ∈ s.sup V := hs.symm ▸ trivial
  rw [Finset.sup_eq_iSup] at hz
  obtain ⟨x, hx⟩ := Opens.mem_iSup.mp hz
  obtain ⟨hxs, hxV⟩ := Opens.mem_iSup.mp hx
  exact ⟨x, hxs, hxV⟩

variable (k : Type u) [Field k] [PerfectField k]

attribute [local instance] openThomCorSheafify openThomSmoothSheafify

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "S" => Spec (CommRingCat.of k)
local notation "M" => effectiveSmoothMotive k

set_option quotPrecheck false in
local notation "Tate(" c ")" =>
  (Stabilization.iterate (effectiveLefschetzTwistFunctor k) c).obj ((M).obj (SmoothSite.base S))

attribute [local instance] normalBundleOrientationAbelian

attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable
  normalBundleOfSmooth normalBundleProjection relativeOpenRestrictionPair effectivePairMotiveFunctor

section Cover

variable {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X)
  [IsClosedImmersion i.left]
  {n m : ℕ} (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)

local notation "p" => normalBundleProjection i hX hZ
set_option quotPrecheck false in
local notation "a₀" => closedPairOpenInclusion (normalBundleZeroSection i hX hZ).left
local notation "F" => conormalSheafDegreeOne i.left
set_option quotPrecheck false in
local notation "r(" U ")" => normalBundleThomRestriction k i hX hZ U

set_option Elab.async false in
set_option maxHeartbeats 1100000 in
-- Use the selected cover and the established restriction formula on its affine subopens.
private theorem normalBundleThomClass_restrict_chosen :
    let H := exists_finset_integral_normalBundleBasisCover k i hX hZ
    let V := H.choose
    let b := H.choose_spec.choose
    let s := H.choose_spec.choose_spec.choose
    ∀ x ∈ s, ∀ (W : Z.left.affineOpens) (h : W.1 ≤ (V x).1),
      r(W.1) ≫ normalBundleThomClass.{u, w, w', w''} k i hX hZ =
        normalBundleBasisThomClass.{u, w, w', w''} k i hX hZ W
          (Modules.vectorBundleBasisRestrict (F) (b x) h) := by
  intro H V b s x hx W hW
  let hs := H.choose_spec.choose_spec.choose_spec.1
  let hi := H.choose_spec.choose_spec.choose_spec.2
  let hz U := normalBundleThomClass_shift_vanishing k i hX hZ V s b hs U 1 (by decide)
  let hc x y := normalBundleBasisThomClass_agree k i hX hZ V b x y (hi x)
  let Q := relativeOpenRestrictionMotive k (p) (a₀)
  let r₀ := Q.map (homOfLE (le_top : W.1 ≤ ⊤))
  let e₀ := (relativeOpenRestrictionTopIso k (p) (a₀)).hom
  let τ := normalBundleThomClass.{u, w, w', w''} k i hX hZ
  let τ' := normalBundleThomClassOfCharts k i hX hZ V s b hs hz hc
  have ht : τ = τ' := normalBundleThomClass_eq_of_chosenCover k i hX hZ
  have hW' := normalBundleThomClassOfCharts_restrict_subopen k i hX hZ V s b hs hz hc x hx W hW
  change (r₀ ≫ e₀) ≫ τ = _
  exact (Category.assoc r₀ e₀ τ).trans ((congrArg (fun t => r₀ ≫ e₀ ≫ t) ht).trans hW')

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
-- Convert the actual inclusions to the maps into the finite union of charts.
private theorem normalBundleThomClass_ext_of_cover
    (V : Z.left → Z.left.affineOpens)
    (b : ∀ x, Module.Basis (Fin (n - m)) Γ(Z.left, (V x).1) Γ(F, (V x).1))
    (s : Finset Z.left) (hs : s.sup (fun x => (V x).1) = ⊤)
    (hi : ∀ x, IsIntegral (V x).1.toScheme)
    (t₁ t₂ : effectivePairMotive k (a₀) ⟶ Tate(n - m))
    (h₁ : ∀ x ∈ s, r((V x).1) ≫ t₁ =
      normalBundleBasisThomClass.{u, w, w', w''} k i hX hZ (V x) (b x))
    (h₂ : ∀ x ∈ s, r((V x).1) ≫ t₂ =
      normalBundleBasisThomClass.{u, w, w', w''} k i hX hZ (V x) (b x)) :
    t₁ = t₂ := by
  let Q := relativeOpenRestrictionMotive k (p) (a₀)
  let d : s.sup (fun x => (V x).1) ≅ (⊤ : Z.left.Opens) := eqToIso hs
  let e := Q.mapIso d ≪≫ relativeOpenRestrictionTopIso k (p) (a₀)
  have hmap (x : Z.left) (hx : x ∈ s) :
      Q.map (homOfLE (Finset.le_sup hx)) ≫ e.hom = r((V x).1) := by
    change _ ≫ Q.map d.hom ≫ (relativeOpenRestrictionTopIso k (p) (a₀)).hom = _
    rw [← Q.map_comp_assoc]
    rfl
  have hunique := existsUnique_normalBundleThomClass k i hX hZ V s b
    (fun U => normalBundleThomClass_shift_vanishing k i hX hZ V s b hs U 1 (by decide))
    (fun x y => normalBundleBasisThomClass_agree k i hX hZ V b x y (hi x))
  apply (cancel_epi e.hom).1
  apply hunique.unique
  · intro x hx
    rw [← Category.assoc, hmap x hx, h₁ x hx]
  · intro x hx
    rw [← Category.assoc, hmap x hx, h₂ x hx]

end Cover

section Restriction

variable {Z X Z' X' : SmoothSite (Spec (CommRingCat.of k))} {i : Z ⟶ X} {j : Z' ⟶ X'}
  [IsClosedImmersion i.left] [IsClosedImmersion j.left]
  {f : X ⟶ X'} {g : Z ⟶ Z'} (h : IsPullback i.left g.left f.left j.left)
  [Flat f.left] [IsOpenImmersion g.left]
  {n m : ℕ} (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)
  (hX' : RelativeDimension X'.hom n) (hZ' : RelativeDimension Z'.hom m)

local notation "p" => normalBundleProjection i hX hZ
local notation "p'" => normalBundleProjection j hX' hZ'
set_option quotPrecheck false in
local notation "a₀" => closedPairOpenInclusion (normalBundleZeroSection i hX hZ).left
set_option quotPrecheck false in
local notation "a₁" => closedPairOpenInclusion (normalBundleZeroSection j hX' hZ').left
local notation "t" => normalBundleThomClass k i hX hZ
local notation "t'" => normalBundleThomClass k j hX' hZ'
local notation "bₙ" => effectiveNormalFibreSupportMap k h
set_option quotPrecheck false in
local notation "r(" U ")" => normalBundleThomRestriction k i hX hZ U
set_option Elab.async false in
set_option maxHeartbeats 1500000 in
-- Refine both normalized chart covers and transport target frames along the open centre map.
/-- The normalized Thom class is preserved by flat base change along an open map of centres. -/
theorem normalBundleThomClass_baseChange :
    (bₙ) ≫ (t') = (t) := by
  classical
  let H := exists_finset_integral_normalBundleBasisCover k i hX hZ
  let V := H.choose
  let b := H.choose_spec.choose
  let s := H.choose_spec.choose_spec.choose
  let hs := H.choose_spec.choose_spec.choose_spec.1
  let hIsInt := H.choose_spec.choose_spec.choose_spec.2
  let H' := exists_finset_integral_normalBundleBasisCover k j hX' hZ'
  let V' := H'.choose
  let b' := H'.choose_spec.choose
  let s' := H'.choose_spec.choose_spec.choose
  let hs' := H'.choose_spec.choose_spec.choose_spec.1
  have hs₀ := normalBundleThomClass_restrict_chosen k i hX hZ
  have hs₁ := normalBundleThomClass_restrict_chosen k j hX' hZ'
  have hex (z : Z.left) :
      ∃ (W : Z.left.affineOpens)
        (c : Module.Basis (Fin (n - m)) Γ(Z.left, W.1) Γ(conormalSheafDegreeOne i.left, W.1)),
        z ∈ W.1 ∧ IsIntegral W.1.toScheme ∧
        r(W.1) ≫ (t) = normalBundleBasisThomClass k i hX hZ W c ∧
        r(W.1) ≫ (bₙ) ≫ (t') = normalBundleBasisThomClass k i hX hZ W c := by
    obtain ⟨x, hx, hzx⟩ := exists_mem_finset_open_cover (fun x => (V x).1) s hs z
    obtain ⟨y, hy, hzy⟩ := exists_mem_finset_open_cover (fun y => (V' y).1) s' hs' (g.left z)
    obtain ⟨W₀, hW₀, hzW₀, hsub⟩ := exists_isAffineOpen_mem_and_subset
      (show z ∈ (V x).1 ⊓ g.left ⁻¹ᵁ (V' y).1 from ⟨hzx, hzy⟩)
    let T₀ := g.left ''ᵁ W₀
    have hT₀ : IsAffineOpen T₀ := by
      let : IsAffine W₀.toScheme := hW₀
      simpa only [T₀, Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι] using
        isAffineOpen_opensRange (W₀.ι ≫ g.left)
    let T : Z'.left.affineOpens := ⟨T₀, hT₀⟩
    have hpre : g.left ⁻¹ᵁ T.1 = W₀ := g.left.preimage_image_eq W₀
    have hTa : T.1 ≤ g.left.opensRange := g.left.image_le_opensRange _
    have hTb : T.1 ≤ (V' y).1 := by
      rintro _ ⟨w, hw, rfl⟩
      exact (hsub hw).2
    let W : Z.left.affineOpens := ⟨g.left ⁻¹ᵁ T.1, hpre.symm ▸ hW₀⟩
    have hW : W.1 ≤ (V x).1 :=
      (le_of_eq hpre).trans (hsub.trans inf_le_left)
    have hzW : z ∈ W.1 :=
      Eq.mp (congrArg (fun B : Z.left.Opens => z ∈ B) hpre.symm) hzW₀
    let : Nonempty W.1.toScheme := ⟨⟨z, hzW⟩⟩
    let : IsIntegral (V x).1.toScheme := hIsInt x
    have hIW : IsIntegral W.1.toScheme :=
      isIntegral_of_isOpenImmersion (Z.left.homOfLE hW)
    let : IsIntegral ((opensFunctor Z).obj W.1).left := hIW
    let c' := Modules.vectorBundleBasisRestrict (conormalSheafDegreeOne j.left) (b' y) hTb
    obtain ⟨c, hc⟩ := exists_conormalBasisBaseChange_open h T.1 hTa c'
    refine ⟨W, c, hzW, hIW, ?_, ?_⟩
    · exact (hs₀ x hx W hW).trans (normalBundleBasisThomClass_eq k i hX hZ W _ c)
    · exact normalBundleBasisThomClass_baseChange k h hX hZ hX' hZ' T W.2 c' c hc
        (hs₁ y hy T hTb)
  choose W c hW hi hsrc htgt using hex
  let U (z : Z.left) := (W z).1
  have htop : (⨆ z, U z) = ⊤ := by
    apply top_unique
    intro z _
    exact Opens.mem_iSup.mpr ⟨z, hW z⟩
  let : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace (Y := S) Z.hom
  have hcompact : IsCompactElement (⊤ : Z.left.Opens) :=
    (Opens.isCompactElement_iff _).mpr isCompact_univ
  obtain ⟨q, hq⟩ := (isCompactElement_iff_exists_le_iSup_of_le_iSup _).mp hcompact Z.left U
    (by rw [htop])
  exact normalBundleThomClass_ext_of_cover k i hX hZ W c q (top_unique hq) hi
    ((bₙ) ≫ (t')) (t) (fun z _ => htgt z)
    (fun z _ => hsrc z)

end Restriction

end AlgebraicGeometry.MotivicHomotopy
