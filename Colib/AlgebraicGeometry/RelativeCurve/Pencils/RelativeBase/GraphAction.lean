/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedGraphSpan
public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedOpenExtension
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.RelativeIdealProduct
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RestrictionDifference.RetainedPencilActions
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CanonicalBoundaryFrame
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.OriginalInfinitySections
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.SectionCorrespondences
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedFamilyRestriction

/-!
# Action of the prescribed graph correction on the original target

The original numerator and graph times the same pole agree on the whole
infinity scheme. Their interpolation acts by the same transfer. The exact
ideal product at the graph endpoint cancels the full pole with its original
multiplicities.

This follows the original identity action in
`Motivic.Transfers.Presheaf.Actions.Pencils.Restriction`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Ample Stacks.Divisors

universe u w

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

open Scheme.PolynomialSectionPencil Scheme.SmoothSite.Contraction

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

local instance (X : Scheme.{u}) (L : X.Modules) [hL : IsInvertibleModule X L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := hL

section Diagonal

variable {S C Y : Scheme.{u}} (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j]

local notation "b" => j ≫ π
local notation "iY" => retainedProductInclusion b π j
local notation "diag" => relativeGraph b b (𝟙 Y) (Category.id_comp b)

/-- The full compactification graph restricted to the original target is the
actual diagonal, with its scheme structure. -/
theorem originalTargetGraph_comap :
    (compactificationGraph π j).ker.comap iY =
      relativeGraphIdeal b b (𝟙 Y) (Category.id_comp b) := by
  have hg : diag ≫ iY = compactificationGraph π j := by
    apply pullback.hom_ext
    · simp only [Category.assoc, retainedProductInclusion_fst, relativeGraph_fst]
    · simp only [Category.assoc, retainedProductInclusion_snd,
        relativeGraph_snd_assoc, relativeGraph_snd, Category.id_comp]
  have H : IsPullback diag (𝟙 Y) iY (compactificationGraph π j) :=
    { w := hg.trans (Category.id_comp _).symm
      isLimit' := ⟨PullbackCone.isLimitAux' _ (fun t ↦ by
        refine ⟨t.snd, ?_, Category.comp_id _, ?_⟩
        · apply (cancel_mono iY).1
          change (t.snd ≫ diag) ≫ iY = t.fst ≫ iY
          exact (Category.assoc _ _ _).trans ((congrArg (t.snd ≫ ·) hg).trans t.condition.symm)
        · intro m _ hm
          exact (Category.comp_id m).symm.trans hm)⟩ }
  exact (ker_eq_comap_of_cartesian H).symm

end Diagonal

variable {S X C Y A Z D : Scheme.{u}}
  {q : X ⟶ S} [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  {π : C ⟶ S} [IsProper π]
  {j : Y ⟶ C} [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  {p : Y ⟶ X} {hq : j ≫ π = p ≫ q} {a : A ⟶ X}
  {z : Z ⟶ X} {s : Z ⟶ Y} {hs : s ≫ p = z} {H : IsPullback s (𝟙 Z) p z}
  {e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf}
  {d : D ⟶ C} {hd : Disjoint (Set.range j) (Set.range d)}
  {ha : Disjoint (Set.range a) (Set.range z)}

namespace SectionData

local notation "b" => j ≫ π
local notation "G" => Scheme.Hom.ker (compactificationGraph π j)
local notation "F" => divisorSheaf G
local notation "σ" => divisorSheafGlobalSection G
local notation "iA" => fullGraphBoundaryMap π j s d
local notation "i∞" => infinityProductMap π j d

variable {k : Type u} [Field k] (t : S ⟶ Spec (.of k)) [Smooth t]
  [IsAffine S] [IsAffine Y]
  {V : Scheme.{u}} [IsAffine V] (v : V ⟶ C) [IsOpenImmersion v]
  [SmoothOfRelativeDimension 1 (v ≫ π)]
  (hc : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))
  (u : V ⟶ Y) (hu : u ≫ j = v)

local instance : Smooth (j ≫ π) := SmoothOfRelativeDimension.smooth 1 (j ≫ π)
local instance : Smooth (v ≫ π) := SmoothOfRelativeDimension.smooth 1 (v ≫ π)

local notation "iV" => retainedProductInclusion b π v
local notation "iY" => retainedProductInclusion b π j
local notation "U" => SmoothSite.mk (b ≫ t)
local notation "W" => SmoothSite.mk ((v ≫ π) ≫ t)
local notation "u₀" => SmoothSite.homMk (X := W) (Y := U) u
  (Eq.trans (Eq.symm (Category.assoc u (j ≫ π) t))
    (congrArg (fun f => f ≫ t)
      (Eq.trans (Eq.symm (Category.assoc u j π)) (congrArg (fun f => f ≫ π) hu))))

set_option maxHeartbeats 600000 in
-- Elaborate both whole support comparisons and the relative graph product on the native sites.
/-- The same numerator-minus-pole acts by the identity after the original
target inclusion. -/
theorem transfer_lambda_comp_graph_eq_id
    (c : SectionData q π j p hq a z s hs H e d hd ha)
    (P : PresheafWithTransfers.{w} k)
    (hP : P.IsA1Invariant) :
    let lambdaSpan : Cor.mk U ⟶ Cor.mk W := c.lambda (k := k) t v hc
    PresheafWithTransfers.transfer P (lambdaSpan ≫ (Cor.graphFunctor k).map u₀) =
      PresheafWithTransfers.transfer P ((Cor.graphFunctor k).map (𝟙 U)) := by
  let sourceSite : SmoothSite (Spec (.of k)) := U
  let retainedSite : SmoothSite (Spec (.of k)) := W
  let inclusion : retainedSite ⟶ sourceSite := u₀
  let := c.T_invertible
  let hGraph : IsInvertibleModule (pullback b π) (tensorModules F c.T) :=
    @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf (pullback b π) F c.T
      (inferInstanceAs (IsInvertibleModule (pullback b π) F)) c.T_invertible
  let := hGraph
  let := retainedProduct_affine b π j
  let := retainedProduct_smooth b π j
  let L := (Modules.pullback iY).obj (tensorModules F c.T)
  let T := (Modules.pullback iY).obj c.T
  let : IsInvertibleModule (retainedProduct b π j) L :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _ iY _ hGraph
  let : IsInvertibleModule (retainedProduct b π j) T :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _ iY
      c.T c.T_invertible
  let : IsInvertibleModule _ ((Modules.pullback i∞).obj (tensorModules F c.T)) :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _ i∞ _ hGraph
  let : IsInvertibleModule _ ((Modules.pullback i∞).obj c.T) :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _ i∞
      c.T c.T_invertible
  let y₀ : Γ(L, ⊤) := pullbackGlobalSections iY _ c.lambdaStartSection
  let y₁ : Γ(L, ⊤) := pullbackGlobalSections iY _ c.aS
  let pole : Γ(T, ⊤) := pullbackGlobalSections iY c.T c.bS
  have hStart : zeroScheme _ ((Modules.pullback i∞).obj (tensorModules F c.T))
      (pullbackGlobalSections i∞ _ c.lambdaStartSection) = ⊤ :=
    (congrArg (fun x => zeroScheme _ ((Modules.pullback i∞).obj (tensorModules F c.T)) x)
      c.lambdaSections_infinity_eq).trans
      (lambda_infinity_zero_of_boundary_zero (π := π) (j := j) (s := s) (d := d) _
        c.aS c.numerator_zero)
  have hPole : zeroScheme _ ((Modules.pullback i∞).obj c.T)
      (pullbackGlobalSections i∞ c.T c.bS) = ⊤ :=
    lambda_infinity_zero_of_boundary_zero (π := π) (j := j) (s := s) (d := d) _
      c.bS c.denominator_zero
  let frame := frameOfZeroSchemeTop _ (pullbackGlobalSections i∞ _ c.lambdaStartSection) hStart
  have hcover := originalRetainedProduct_infinity_cover b π v j u hu s d hc
  have hfamily := finite_flat_retainedFamily_of_boundary_frame iY (b ≫ t)
    (pullback.fst b π) i∞ _ c.lambdaStartSection c.aS hcover
    c.lambdaSections_infinity_eq frame.hom (frameOfZeroSchemeTop_section _ _ _)
  have hfamily' :=
    (congrArg (fun p : retainedProduct b π j ⟶ Y =>
      IsFinite (familySource (b ≫ t) p L y₀ y₁) ∧ Flat (familySource (b ≫ t) p L y₀ y₁))
      (retainedProductInclusion_fst b π j)).mp hfamily
  let := hfamily'.1
  let := hfamily'.2
  have hFamilyFin : IsFinite (Cor.nativeRetainedFamilySource (k := k) t b b L y₀ y₁) := by
    unfold Cor.nativeRetainedFamilySource
    infer_instance
  have hFamilyFlat : Flat (Cor.nativeRetainedFamilySource (k := k) t b b L y₀ y₁) := by
    unfold Cor.nativeRetainedFamilySource
    infer_instance
  let hZero := Cor.nativeRetainedZero_finite_flat (k := k) t b b L y₀ y₁
    (_hFamilyFin := hFamilyFin) (_hFamilyFlat := hFamilyFlat)
  let hZeroFin := hZero.1
  let hZeroFlat := hZero.2
  let hOne := Cor.nativeRetainedOne_finite_flat (k := k) t b b L y₀ y₁
    (_hFamilyFin := hFamilyFin) (_hFamilyFlat := hFamilyFlat)
  let hOneFin := hOne.1
  let hOneFlat := hOne.2
  have hPY := (congrArg (fun p : retainedProduct b π j ⟶ Y =>
    IsFinite ((zeroScheme _ T pole).subschemeι ≫ p) ∧
      IsRelativeEffectiveCartierDivisor p (zeroScheme _ T pole))
    (retainedProductInclusion_fst b π j)).mp
      (finite_relativeCartier_of_boundary_zero i∞ (pullback.fst b π) iY hcover c.T c.bS hPole)
  let := hPY.1
  let := hPY.2.2
  let IA := zeroScheme (pullback b π) (tensorModules F c.T) c.aS
  let IB := zeroScheme (pullback b π) c.T c.bS
  have hAB := c.retainedFirstFactors_comap_finite_relativeCartier v hc
  let : IsNoetherian Y := isNoetherian_of_finiteType_of_isNoetherian (b ≫ t)
  let : IsAffineHom ((v ≫ π) ≫ t) := isAffineHom_of_isAffine _
  have hfull := lambdaBoundary_retained_cover π j s d v hc
  have hA : Set.range IA.subschemeι ⊆ Set.range iV :=
    whole_support_subset_of_boundary_comap_top iV iA IA hfull
      ((zeroScheme_pullback iA _ c.aS).symm.trans c.numerator_zero)
  have hB : Set.range IB.subschemeι ⊆ Set.range iV :=
    whole_support_subset_of_boundary_comap_top iV iA IB hfull
      ((zeroScheme_pullback iA c.T c.bS).symm.trans c.denominator_zero)
  let KA := IA.comap iV
  let JA := zeroScheme _ L y₁
  obtain ⟨eA, hfA, hgA⟩ := exists_retainedSupportOpenExtensionIso b π v j u hu
    IA KA rfl JA (zeroScheme_pullback iY _ c.aS) hA
  let aV : Cor.mk sourceSite ⟶ Cor.mk retainedSite :=
    Cor.ofFiniteFlatSpanRaw (b ≫ t) ((v ≫ π) ≫ t)
      (KA.subschemeι ≫ pullback.fst b (v ≫ π)) (KA.subschemeι ≫ pullback.snd b (v ≫ π))
      (hFin := hAB.1.1) (hFlat := hAB.1.2.2)
      (Cor.relativeSupport_legs_over_base b (v ≫ π) t KA)
  have hRetainedA : (KA.subschemeι ≫ pullback.fst b (v ≫ π)) ≫ sourceSite.hom =
      (KA.subschemeι ≫ pullback.snd b (v ≫ π)) ≫ retainedSite.hom :=
    Cor.relativeSupport_legs_over_base b (v ≫ π) t KA
  have hOriginalA : (JA.subschemeι ≫ pullback.fst b b) ≫ sourceSite.hom =
      (JA.subschemeι ≫ pullback.snd b b) ≫ sourceSite.hom :=
    Cor.relativeSupport_legs_over_base b b t JA
  let extensionA : Cor.SpanGraphIsomorphismData (k := k) sourceSite retainedSite
      sourceSite inclusion KA.subscheme JA.subscheme := {
    source := KA.subschemeι ≫ pullback.fst b (v ≫ π)
    sourceFinite := hAB.1.1
    sourceFlat := hAB.1.2.2
    target := KA.subschemeι ≫ pullback.snd b (v ≫ π)
    overBase := hRetainedA
    originalSource := JA.subschemeι ≫ pullback.fst b b
    originalFinite := hOneFin
    originalFlat := hOneFlat
    originalTarget := JA.subschemeι ≫ pullback.snd b b
    originalOverBase := hOriginalA
    supportIso := eA
    source_eq := hfA
    target_eq := by
      change eA.hom ≫ (JA.subschemeι ≫ pullback.snd b b) =
        (KA.subschemeι ≫ pullback.snd b (v ≫ π)) ≫ u
      simpa only [Category.assoc] using hgA }
  have hAopen : aV ≫ (Cor.graphFunctor k).map inclusion =
      Cor.retainedZeroSpan (k := k) t b b L y₁ hOneFin hOneFlat :=
    Cor.SpanGraphIsomorphismData.comp_graph_eq (k := k) extensionA
  let KB := IB.comap iV
  let JB := zeroScheme _ T pole
  obtain ⟨eB, hfB, hgB⟩ := exists_retainedSupportOpenExtensionIso b π v j u hu
    IB KB rfl JB (zeroScheme_pullback iY _ c.bS) hB
  let bV : Cor.mk sourceSite ⟶ Cor.mk retainedSite :=
    Cor.ofFiniteFlatSpanRaw (b ≫ t) ((v ≫ π) ≫ t)
      (KB.subschemeι ≫ pullback.fst b (v ≫ π)) (KB.subschemeι ≫ pullback.snd b (v ≫ π))
      (hFin := hAB.2.1) (hFlat := hAB.2.2.2)
      (Cor.relativeSupport_legs_over_base b (v ≫ π) t KB)
  have hRetainedB : (KB.subschemeι ≫ pullback.fst b (v ≫ π)) ≫ sourceSite.hom =
      (KB.subschemeι ≫ pullback.snd b (v ≫ π)) ≫ retainedSite.hom :=
    Cor.relativeSupport_legs_over_base b (v ≫ π) t KB
  have hOriginalB : (JB.subschemeι ≫ pullback.fst b b) ≫ sourceSite.hom =
      (JB.subschemeι ≫ pullback.snd b b) ≫ sourceSite.hom :=
    Cor.relativeSupport_legs_over_base b b t JB
  let extensionB : Cor.SpanGraphIsomorphismData (k := k) sourceSite retainedSite
      sourceSite inclusion KB.subscheme JB.subscheme := {
    source := KB.subschemeι ≫ pullback.fst b (v ≫ π)
    sourceFinite := hAB.2.1
    sourceFlat := hAB.2.2.2
    target := KB.subschemeι ≫ pullback.snd b (v ≫ π)
    overBase := hRetainedB
    originalSource := JB.subschemeι ≫ pullback.fst b b
    originalFinite := hPY.1
    originalFlat := hPY.2.2
    originalTarget := JB.subschemeι ≫ pullback.snd b b
    originalOverBase := hOriginalB
    supportIso := eB
    source_eq := hfB
    target_eq := by
      change eB.hom ≫ (JB.subschemeι ≫ pullback.snd b b) =
        (KB.subschemeι ≫ pullback.snd b (v ≫ π)) ≫ u
      simpa only [Category.assoc] using hgB }
  have hBopen : bV ≫ (Cor.graphFunctor k).map inclusion =
      Cor.retainedZeroSpan (k := k) t b b T pole hPY.1 hPY.2.2 :=
    Cor.SpanGraphIsomorphismData.comp_graph_eq (k := k) extensionB
  let dg := relativeGraphIdeal b b (𝟙 Y) (Category.id_comp b)
  have hGraphFin : IsFinite (dg.subschemeι ≫ pullback.fst b b) := by
    change IsFinite
      ((relativeGraphIdeal b b (𝟙 Y) (Category.id_comp b)).subschemeι ≫ pullback.fst b b)
    rw [← relativeGraphSupportIso_hom_base]
    infer_instance
  have hGraphFlat : Flat (dg.subschemeι ≫ pullback.fst b b) := by
    change Flat
      ((relativeGraphIdeal b b (𝟙 Y) (Category.id_comp b)).subschemeι ≫ pullback.fst b b)
    rw [← relativeGraphSupportIso_hom_base]
    infer_instance
  have hGraphPole : zeroScheme (pullback b π) (tensorModules F c.T) c.lambdaStartSection =
      G * zeroScheme (pullback b π) c.T c.bS :=
    (zeroScheme_tensorSection_eq_mul F c.T σ c.bS).trans
      (congrArg (fun I : (pullback b π).IdealSheafData =>
        I * zeroScheme (pullback b π) c.T c.bS) (zeroScheme_canonicalSection G))
  have hprod : zeroScheme _ L y₀ = dg * zeroScheme _ T pole :=
    (zeroScheme_pullback iY _ c.lambdaStartSection).trans
      ((congrArg (fun I : (pullback b π).IdealSheafData => I.comap iY) hGraphPole).trans
        ((Stacks.IdealSheaf.comap_mul G (zeroScheme (pullback b π) c.T c.bS) iY).trans
          (congrArg₂ (· * ·) (originalTargetGraph_comap π j)
            (zeroScheme_pullback iY c.T c.bS).symm)))
  have hadd := Cor.retainedSpan_add_of_ideal_product (k := k) t b b dg (zeroScheme _ T pole)
    (zeroScheme _ L y₀) (isLocallyPrincipal_of_isEffectiveCartierDivisor dg inferInstance)
    hPY.2.1 hprod
  let : IsFinite (dg.subschemeι ≫ pullback.fst b b) := hGraphFin
  let : Flat (dg.subschemeι ≫ pullback.fst b b) := hGraphFlat
  have hId : (𝟙 Y) ≫ (b ≫ t) = (𝟙 Y) ≫ (b ≫ t) := rfl
  have hGraphId : Cor.ofFiniteFlatSpanRaw (b ≫ t) (b ≫ t) (𝟙 Y) (𝟙 Y) hId =
      (Cor.graphFunctor k).map (𝟙 sourceSite) :=
    Cor.ofFiniteFlatSpan_id_left (k := k) (𝟙 sourceSite)
  have hgraph : Cor.retainedIdealSpan (k := k) t b b dg =
      (Cor.graphFunctor k).map (𝟙 sourceSite) :=
    (Cor.ofFiniteFlatSpanRaw_relativeGraph_eq_id_left t b b (𝟙 Y) (Category.id_comp b) hId).trans
      hGraphId
  have he := PresheafWithTransfers.transfer_retainedZeroSchemes_eq (k := k) t b b L y₀ y₁ P hP
    (hFamilyFin := hFamilyFin) (hFamilyFlat := hFamilyFlat)
  change PresheafWithTransfers.transfer P (X := Cor.mk sourceSite) (Y := Cor.mk sourceSite)
    ((aV - bV) ≫ (Cor.graphFunctor k).map inclusion) = _
  rw [Preadditive.sub_comp, hAopen, hBopen, PresheafWithTransfers.transfer_sub, ← he]
  have hstart : Cor.retainedZeroSpan (k := k) t b b L y₀ hZeroFin hZeroFlat =
      Cor.retainedIdealSpan (k := k) t b b dg +
        Cor.retainedZeroSpan (k := k) t b b T pole hPY.1 hPY.2.2 :=
    hadd
  rw [hstart, PresheafWithTransfers.transfer_add, add_sub_cancel_right]
  exact congrArg
    (PresheafWithTransfers.transfer P (X := Cor.mk sourceSite) (Y := Cor.mk sourceSite)) hgraph

end SectionData

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
