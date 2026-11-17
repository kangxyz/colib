/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ThomGraphNaturality
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Naturality of the supported Thom graph on open restrictions -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
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
local notation "M" => effectiveSmoothMotive k
local notation "Φ" => effectivePairMotiveFunctor k

attribute [local instance] thomGraphBasicBaseNoetherian thomGraphBasicAbelian thomGraphBasicMonoidal

attribute [local irreducible] effectivePairThomGraph effectiveRestrictedThomGraph
attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable

set_option maxHeartbeats 1800000 in
-- Use the original restricted pair and the inverse product comparison.
/-- Restricting the class to a chart agrees with applying it after the graph into the
fixed original pair. -/
theorem effectiveRestrictedThomGraph_eq_restrict {A V Z : Sm} (p : V ⟶ Z) (j : A ⟶ V)
    [IsOpenImmersion j.left] (W : Z.left.Opens) {K : E}
    (t : effectivePairMotive k j ⟶ K) :
    effectiveRestrictedThomGraph k p j W t =
      effectivePairThomGraph k (j := preimageOpenMap V j (p.left ⁻¹ᵁ W))
        (preimageOpenMap Z p W)
        (((relativeOpenRestrictionMotive k p j).map (homOfLE (le_top : W ≤ ⊤)) ≫
          (relativeOpenRestrictionTopIso k p j).hom) ≫ t) := by
  let P := relativeOpenRestrictionMotive k p j
  let F := relativeOpenRestrictionPair k p j
  let Y := (opensFunctor Z).obj W
  let a := preimageOpenMap V j (p.left ⁻¹ᵁ W)
  let a₀ := F.map (homOfLE (le_top : W ≤ ⊤))
  let f : Arrow.mk a ⟶ Arrow.mk j :=
    a₀ ≫ pairArrowOpenInclusion j (p.left ⁻¹ᵁ (⊤ : Z.left.Opens))
  let q := preimageOpenMap Z p W
  let aGraph := pairProductGraph a q
  let d₀ := (parameterProduct Y).mapArrow.map f
  let u : Arrow.mk a ⟶ (parameterProduct Y).mapArrow.obj (Arrow.mk j) :=
    openRestrictionProductGraphArrowMap p j W
  let b : effectivePairMotive k a ⟶ effectivePairMotive k j := (Φ).map f
  let r : effectivePairMotive k a ⟶ effectivePairMotive k j :=
    P.map (homOfLE (le_top : W ≤ ⊤)) ≫ (relativeOpenRestrictionTopIso k p j).hom
  let aₘ : effectivePairMotive k a ⟶ effectivePairMotive k ((parameterProduct Y).map a) :=
    (Φ).map aGraph
  let d : effectivePairMotive k ((parameterProduct Y).map a) ⟶
      effectivePairMotive k ((parameterProduct Y).map j) :=
    (Φ).map d₀
  let uₘ : effectivePairMotive k a ⟶ effectivePairMotive k ((parameterProduct Y).map j) :=
    (Φ).map u
  let T : E ⥤ E := tensorRight ((M).obj Y)
  let : IsOpenImmersion a.left := preimageOpenMap_isOpenImmersion V j (p.left ⁻¹ᵁ W)
  let e := effectivePairProductRightIso k a Y
  let e' := effectivePairProductRightIso k j Y
  have hright : f.right = SmoothSite.openInclusion V (p.left ⁻¹ᵁ W) :=
    MorphismProperty.Over.Hom.ext (Scheme.homOfLE_ι V.left
      (p.left.preimage_mono (le_top : W ≤ ⊤)))
  have hgraph : aGraph ≫ d₀ = u := by
    let g := (parameterProduct Y).map (Arrow.mk j).hom
    let : IsOpenImmersion g.left := parameterProduct_map_isOpenImmersion Y j
    apply openPairArrowMap_eq_of_right (f' := g)
    change productGraph q ≫ SmoothSite.productMap f.right (𝟙 Y) =
      productLift (SmoothSite.openInclusion V (p.left ⁻¹ᵁ W)) q
    rw [hright]
    exact productGraph_preimageOpenMap_comp_productMap p W
  have hs : CommSq (T.map b) e.hom e'.hom d :=
    ⟨effectivePairProductRightIso_naturality k f Y⟩
  have hn := (hs.vert_inv).w_assoc (T.map t)
  have hb : r = b := by
    dsimp only [r]
    rw [relativeOpenRestrictionTopIso_hom]
    exact ((Φ).map_comp a₀ (pairArrowOpenInclusion j (p.left ⁻¹ᵁ (⊤ : Z.left.Opens)))).symm
  have hd : aₘ ≫ d = uₘ := ((Φ).map_comp aGraph d₀).symm.trans ((Φ).congr_map hgraph)
  have hf : T.map (r ≫ t) = T.map b ≫ T.map t :=
    (T.congr_map (congrArg (· ≫ t) hb)).trans (T.map_comp b t)
  unfold effectiveRestrictedThomGraph effectivePairThomGraph
  change uₘ ≫ e'.inv ≫ T.map t = aₘ ≫ e.inv ≫ T.map (r ≫ t)
  calc
    _ = (aₘ ≫ d) ≫ e'.inv ≫ T.map t := congrArg (· ≫ e'.inv ≫ T.map t) hd.symm
    _ = aₘ ≫ d ≫ e'.inv ≫ T.map t := Category.assoc aₘ d _
    _ = aₘ ≫ e.inv ≫ T.map b ≫ T.map t := congrArg (aₘ ≫ ·) hn
    _ = _ := congrArg (fun u => aₘ ≫ e.inv ≫ u) hf.symm

set_option maxHeartbeats 1800000 in
-- Both coordinates use the literal isomorphisms of the top restrictions.
/-- At the whole base, the restriction graph transported along the top identifications
recovers the original projection graph in both coordinates. -/
theorem effectiveRestrictedThomGraph_top {A V Z : Sm} (p : V ⟶ Z) (j : A ⟶ V)
    [IsOpenImmersion j.left] {K : E} (t : effectivePairMotive k j ⟶ K) :
    effectiveRestrictedThomGraph k p j ⊤ t ≫ (K ◁ (M).map (smoothTopOpenIso k Z).hom) =
      (relativeOpenRestrictionTopIso k p j).hom ≫ effectivePairThomGraph k (j := j) p t := by
  let W : Z.left.Opens := ⊤
  let Y := (opensFunctor Z).obj W
  let e := smoothTopOpenIso k Z
  let φ := pairArrowOpenInclusion j (p.left ⁻¹ᵁ W)
  let g : (relativeOpenRestrictionPair k p j).obj W ⟶
      (parameterProduct Y).mapArrow.obj (Arrow.mk j) :=
    openRestrictionProductGraphArrowMap p j W
  let g' := pairProductGraph j p
  let m := smoothParameterArrowMap e.hom (Arrow.mk j)
  let N := (M).map e.hom
  let a := effectivePairProductRightIso k j Y
  let a' := effectivePairProductRightIso k j Z
  have hgraph : g ≫ m = φ ≫ g' := by
    let j' := (parameterProduct Z).map (Arrow.mk j).hom
    let : IsOpenImmersion j'.left := parameterProduct_map_isOpenImmersion Z j
    apply openPairArrowMap_eq_of_right (f' := j')
    change openRestrictionProductGraph p W ≫ SmoothSite.productMap (𝟙 V) e.hom =
      SmoothSite.openInclusion V (p.left ⁻¹ᵁ W) ≫ productGraph p
    change _ ≫ SmoothSite.productMap (𝟙 V) (SmoothSite.openInclusion Z ⊤) = _
    exact openRestrictionProductGraph_top_comp_productMap p
  let gₘ : (relativeOpenRestrictionMotive k p j).obj W ⟶
      effectivePairMotive k ((parameterProduct Y).map j) := (Φ).map g
  let φₘ : (relativeOpenRestrictionMotive k p j).obj W ⟶ effectivePairMotive k j :=
    (Φ).map φ
  let mₘ : effectivePairMotive k ((parameterProduct Y).map j) ⟶
      effectivePairMotive k ((parameterProduct Z).map j) := (Φ).map m
  let gₘ' : effectivePairMotive k j ⟶ effectivePairMotive k ((parameterProduct Z).map j) :=
    (Φ).map g'
  have hφ : (relativeOpenRestrictionTopIso k p j).hom = φₘ :=
    relativeOpenRestrictionTopIso_hom k p j
  have h₁ : CommSq g φ m g' := ⟨hgraph⟩
  have h₂ : CommSq gₘ φₘ mₘ gₘ' := h₁.map (Φ)
  have h₃ : CommSq (effectivePairMotive k j ◁ N) a.hom a'.hom mₘ :=
    ⟨effectivePairProductRightIso_parameter k j e.hom⟩
  have h₄ : CommSq (t ▷ (M).obj Y) (effectivePairMotive k j ◁ N)
      (K ◁ N) (t ▷ (M).obj Z) := ⟨(whisker_exchange t N).symm⟩
  have hf := ((h₂.horiz_comp h₃.vert_inv.flip).horiz_comp h₄).w
  rw [hφ]
  unfold effectiveRestrictedThomGraph effectivePairThomGraph
  change (gₘ ≫ a.inv ≫ (t ▷ (M).obj Y)) ≫ (K ◁ N) =
    φₘ ≫ gₘ' ≫ a'.inv ≫ (t ▷ (M).obj Z)
  simpa only [Category.assoc] using hf

end AlgebraicGeometry.MotivicHomotopy
