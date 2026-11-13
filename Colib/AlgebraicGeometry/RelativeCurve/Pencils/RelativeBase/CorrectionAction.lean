/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedOpenExtension
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RestrictionDifference.RetainedPencilActions
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CanonicalBoundaryFrame
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.OriginalInfinitySections
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.SectionCorrespondences
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedFamilyRestriction

/-!
# Action of the prescribed correction on the original target

The numerator and denominator come from the same whole-boundary prescription.
Their restriction to infinity is equal, so their pencil on the original target
gives equal transfer actions. The two whole supports identify the resulting
correspondences with the actual extension of the retained correction.

This follows the original correction action in
`Motivic.Transfers.Presheaf.Actions.Pencils.Correction`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Ample Stacks.Divisors

universe u w

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

open Scheme.PolynomialSectionPencil Scheme.SmoothSite.Contraction

local instance (X : Scheme.{u}) (L : X.Modules) [hL : IsInvertibleModule X L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := hL

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

local notation "b" => a ≫ q
local notation "iN" => psiBoundaryInclusion q π j p hq a z s hs d
local notation "i∞" => pullback.fst (pullback.snd b π) d

variable {k : Type u} [Field k] (t : S ⟶ Spec (.of k)) [Smooth t]
  [IsAffine S] [IsAffine Y] [IsAffine A] [IsOpenImmersion a]
  {V : Scheme.{u}} [IsAffine V] (v : V ⟶ C) [IsOpenImmersion v]
  [SmoothOfRelativeDimension 1 (v ≫ π)]
  (hc : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))
  (u : V ⟶ Y) (hu : u ≫ j = v)

local instance : Smooth (j ≫ π) := SmoothOfRelativeDimension.smooth 1 (j ≫ π)
local instance : Smooth (v ≫ π) := SmoothOfRelativeDimension.smooth 1 (v ≫ π)
local instance : Smooth q := SmoothOfRelativeDimension.smooth 1 q

local notation "iV" => retainedProductInclusion b π v
local notation "iY" => retainedProductInclusion b π j
local notation "U" => SmoothSite.mk (b ≫ t)
local notation "W" => SmoothSite.mk ((v ≫ π) ≫ t)
local notation "Y₀" => SmoothSite.mk ((j ≫ π) ≫ t)
local notation "u₀" => SmoothSite.homMk (X := W) (Y := Y₀) u
  (Eq.trans (Eq.symm (Category.assoc u (j ≫ π) t))
    (congrArg (fun f => f ≫ t)
      (Eq.trans (Eq.symm (Category.assoc u j π)) (congrArg (fun f => f ≫ π) hu))))

set_option maxHeartbeats 600000 in
-- Elaborate both whole support comparisons on the original source and target sites.
/-- The same correction acts by zero on the original target after the actual
retained inclusion. Both terms have their full scheme structure. -/
theorem transfer_psi_comp_graph_eq_zero
    (c : SectionData q π j p hq a z s hs H e d hd ha)
    (P : PresheafWithTransfers.{w} k)
    (hP : P.IsA1Invariant) :
    let ψ : Cor.mk U ⟶ Cor.mk W := c.psi (k := k) t v hc
    PresheafWithTransfers.transfer P (ψ ≫ (Cor.graphFunctor k).map u₀) = 0 := by
  let sourceSite : SmoothSite (Spec (.of k)) := U
  let retainedSite : SmoothSite (Spec (.of k)) := W
  let originalSite : SmoothSite (Spec (.of k)) := Y₀
  let inclusion : retainedSite ⟶ originalSite := u₀
  let := c.N_invertible
  let := retainedProduct_affine b π j
  let := retainedProduct_smooth b π j
  let F := (Modules.pullback iY).obj c.N
  let : IsInvertibleModule (retainedProduct b π j) F :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _ iY
      c.N c.N_invertible
  let : IsInvertibleModule _ ((Modules.pullback i∞).obj c.N) :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _ i∞
      c.N c.N_invertible
  let dY : Γ(F, ⊤) := pullbackGlobalSections iY c.N c.dS
  let nY : Γ(F, ⊤) := pullbackGlobalSections iY c.N c.nS
  let frame := frameOfZeroSchemeTop _ (pullbackGlobalSections i∞ c.N c.dS)
    c.correctionDenominator_infinity_zero
  have hfamily := finite_flat_retainedFamily_of_boundary_frame iY (b ≫ t)
    (pullback.fst b π) i∞ c.N c.dS c.nS
    (originalRetainedProduct_infinity_cover b π v j u hu s d hc)
    c.correctionSections_infinity_eq.symm frame.hom (frameOfZeroSchemeTop_section _ _ _)
  have hfamily' :=
    (congrArg (fun p : retainedProduct b π j ⟶ A =>
      IsFinite (familySource (b ≫ t) p F dY nY) ∧ Flat (familySource (b ≫ t) p F dY nY))
      (retainedProductInclusion_fst b π j)).mp hfamily
  let := hfamily'.1
  let := hfamily'.2
  have hFamilyFin : IsFinite (Cor.nativeRetainedFamilySource (k := k) t b (j ≫ π) F dY nY) := by
    unfold Cor.nativeRetainedFamilySource
    infer_instance
  have hFamilyFlat : Flat (Cor.nativeRetainedFamilySource (k := k) t b (j ≫ π) F dY nY) := by
    unfold Cor.nativeRetainedFamilySource
    infer_instance
  let hZero := Cor.nativeRetainedZero_finite_flat (k := k) t b (j ≫ π) F dY nY
    (_hFamilyFin := hFamilyFin) (_hFamilyFlat := hFamilyFlat)
  let hZeroFin := hZero.1
  let hZeroFlat := hZero.2
  let hOne := Cor.nativeRetainedOne_finite_flat (k := k) t b (j ≫ π) F dY nY
    (_hFamilyFin := hFamilyFin) (_hFamilyFlat := hFamilyFlat)
  let hOneFin := hOne.1
  let hOneFlat := hOne.2
  let IN := zeroScheme (pullback b π) c.N c.nS
  let ID := zeroScheme (pullback b π) c.N c.dS
  have hND := c.retainedCorrectionFactors_comap_finite_relativeCartier v hc
  let : IsNoetherian A := isNoetherian_of_finiteType_of_isNoetherian (b ≫ t)
  let : IsAffineHom ((v ≫ π) ≫ t) := isAffineHom_of_isAffine _
  have hcover := psiBoundary_retained_cover q π j p hq a z s hs d v hc
  have hN : Set.range IN.subschemeι ⊆ Set.range iV :=
    whole_support_subset_of_boundary_comap_top iV iN IN hcover
      ((zeroScheme_pullback iN c.N c.nS).symm.trans c.correctionNumerator_zero)
  have hD : Set.range ID.subschemeι ⊆ Set.range iV :=
    whole_support_subset_of_boundary_comap_top iV iN ID hcover
      ((zeroScheme_pullback iN c.N c.dS).symm.trans c.correctionDenominator_zero)
  let KD := ID.comap iV
  let JD := zeroScheme _ F dY
  obtain ⟨eD, hfD, hgD⟩ := exists_retainedSupportOpenExtensionIso b π v j u hu
    ID KD rfl JD (zeroScheme_pullback iY _ c.dS) hD
  let dV : Cor.mk sourceSite ⟶ Cor.mk retainedSite :=
    Cor.ofFiniteFlatSpanRaw (b ≫ t) ((v ≫ π) ≫ t)
      (KD.subschemeι ≫ pullback.fst b (v ≫ π)) (KD.subschemeι ≫ pullback.snd b (v ≫ π))
      (hFin := hND.2.1) (hFlat := hND.2.2.2)
      (Cor.relativeSupport_legs_over_base b (v ≫ π) t KD)
  have hRetainedD : (KD.subschemeι ≫ pullback.fst b (v ≫ π)) ≫ sourceSite.hom =
      (KD.subschemeι ≫ pullback.snd b (v ≫ π)) ≫ retainedSite.hom :=
    Cor.relativeSupport_legs_over_base b (v ≫ π) t KD
  have hOriginalD : (JD.subschemeι ≫ pullback.fst b (j ≫ π)) ≫ sourceSite.hom =
      (JD.subschemeι ≫ pullback.snd b (j ≫ π)) ≫ originalSite.hom :=
    Cor.relativeSupport_legs_over_base b (j ≫ π) t JD
  let extensionD : Cor.SpanGraphIsomorphismData (k := k) sourceSite retainedSite
      originalSite inclusion KD.subscheme JD.subscheme := {
    source := KD.subschemeι ≫ pullback.fst b (v ≫ π)
    sourceFinite := hND.2.1
    sourceFlat := hND.2.2.2
    target := KD.subschemeι ≫ pullback.snd b (v ≫ π)
    overBase := hRetainedD
    originalSource := JD.subschemeι ≫ pullback.fst b (j ≫ π)
    originalFinite := hZeroFin
    originalFlat := hZeroFlat
    originalTarget := JD.subschemeι ≫ pullback.snd b (j ≫ π)
    originalOverBase := hOriginalD
    supportIso := eD
    source_eq := hfD
    target_eq := by
      change eD.hom ≫ (JD.subschemeι ≫ pullback.snd b (j ≫ π)) =
        (KD.subschemeι ≫ pullback.snd b (v ≫ π)) ≫ u
      simpa only [Category.assoc] using hgD }
  have hDopen : dV ≫ (Cor.graphFunctor k).map inclusion =
      Cor.retainedZeroSpan (k := k) t b (j ≫ π) F dY hZeroFin hZeroFlat :=
    Cor.SpanGraphIsomorphismData.comp_graph_eq (k := k) extensionD
  let KN := IN.comap iV
  let JN := zeroScheme _ F nY
  obtain ⟨eN, hfN, hgN⟩ := exists_retainedSupportOpenExtensionIso b π v j u hu
    IN KN rfl JN (zeroScheme_pullback iY _ c.nS) hN
  let nV : Cor.mk sourceSite ⟶ Cor.mk retainedSite :=
    Cor.ofFiniteFlatSpanRaw (b ≫ t) ((v ≫ π) ≫ t)
      (KN.subschemeι ≫ pullback.fst b (v ≫ π)) (KN.subschemeι ≫ pullback.snd b (v ≫ π))
      (hFin := hND.1.1) (hFlat := hND.1.2.2)
      (Cor.relativeSupport_legs_over_base b (v ≫ π) t KN)
  have hRetainedN : (KN.subschemeι ≫ pullback.fst b (v ≫ π)) ≫ sourceSite.hom =
      (KN.subschemeι ≫ pullback.snd b (v ≫ π)) ≫ retainedSite.hom :=
    Cor.relativeSupport_legs_over_base b (v ≫ π) t KN
  have hOriginalN : (JN.subschemeι ≫ pullback.fst b (j ≫ π)) ≫ sourceSite.hom =
      (JN.subschemeι ≫ pullback.snd b (j ≫ π)) ≫ originalSite.hom :=
    Cor.relativeSupport_legs_over_base b (j ≫ π) t JN
  let extensionN : Cor.SpanGraphIsomorphismData (k := k) sourceSite retainedSite
      originalSite inclusion KN.subscheme JN.subscheme := {
    source := KN.subschemeι ≫ pullback.fst b (v ≫ π)
    sourceFinite := hND.1.1
    sourceFlat := hND.1.2.2
    target := KN.subschemeι ≫ pullback.snd b (v ≫ π)
    overBase := hRetainedN
    originalSource := JN.subschemeι ≫ pullback.fst b (j ≫ π)
    originalFinite := hOneFin
    originalFlat := hOneFlat
    originalTarget := JN.subschemeι ≫ pullback.snd b (j ≫ π)
    originalOverBase := hOriginalN
    supportIso := eN
    source_eq := hfN
    target_eq := by
      change eN.hom ≫ (JN.subschemeι ≫ pullback.snd b (j ≫ π)) =
        (KN.subschemeι ≫ pullback.snd b (v ≫ π)) ≫ u
      simpa only [Category.assoc] using hgN }
  have hNopen : nV ≫ (Cor.graphFunctor k).map inclusion =
      Cor.retainedZeroSpan (k := k) t b (j ≫ π) F nY hOneFin hOneFlat :=
    Cor.SpanGraphIsomorphismData.comp_graph_eq (k := k) extensionN
  have he := PresheafWithTransfers.transfer_retainedZeroSchemes_eq (k := k) t b (j ≫ π) F dY nY P hP
    (hFamilyFin := hFamilyFin) (hFamilyFlat := hFamilyFlat)
  change PresheafWithTransfers.transfer P (X := Cor.mk sourceSite) (Y := Cor.mk originalSite)
    ((dV - nV) ≫ (Cor.graphFunctor k).map inclusion) = 0
  rw [Preadditive.sub_comp, hDopen, hNopen, PresheafWithTransfers.transfer_sub, he, sub_self]

end SectionData

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
