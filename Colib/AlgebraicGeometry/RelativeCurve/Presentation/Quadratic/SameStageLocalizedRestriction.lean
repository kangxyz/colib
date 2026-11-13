/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.SameStageOriginalMark
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.EtaleChartLocalizedRestrictionPreimage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.EtaleChartLocalizedRestriction

/-! # Restriction for the stored same-stage geometry package

The geometry is stored over the original ground field. This leaf only executes
its existing localized restriction consumer; dimension induction is not asserted.
This integration leaf awaits complete dependency compilation in CI.
-/
@[expose] public noncomputable section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.RelativeCurve
open AlgebraicGeometry.Scheme.SmoothSite.EtaleChart
open Opposite
universe u v
namespace QuadraticIncidence.InfinityChart
attribute [local instance] SameStageLocalizedInputs.ring
  SameStageLocalizedInputs.tailSmooth SameStageLocalizedInputs.tailSeparated
  SameStageLocalizedInputs.tailQuasiCompact SameStageLocalizedInputs.affineA
  SameStageLocalizedInputs.affineZ SameStageLocalizedInputs.etaleQ
  SameStageLocalizedInputs.smoothP SameStageLocalizedInputs.affineU
  SameStageLocalizedInputs.integralN SameStageLocalizedInputs.normalN
  SameStageLocalizedInputs.openJ SameStageLocalizedInputs.properFN
  SameStageLocalizedInputs.smoothU SameStageLocalizedInputs.closedD
  SameStageLocalizedInputs.finiteLocal SameStageLocalizedInputs.finitePi
  SameStageLocalizedInputs.openChart SameStageLocalizedInputs.etaleAE

attribute [local instance] SameStageLocalizedInputs.affineT
  SameStageLocalizedInputs.originalChartEtale

attribute [local instance] LocalizedRestriction.scalar_isOpenImmersion
  LocalizedRestriction.nativeTailAffine
  LocalizedRestriction.localizedTailAffine LocalizedRestriction.localizedCoordinateAffine
  LocalizedRestriction.localizedChartAffine LocalizedRestriction.localizedProjectionSmooth
  LocalizedRestriction.localizedChartEtale

open SmoothSite SmoothSite.EtaleChart.OriginalFixed

local instance {K : Type u} [Field K] : IsAffine (SmoothSite.base (Spec (.of K))).left :=
  inferInstanceAs (IsAffine (Spec (.of K)))

/-- Restriction equality on the exact selected model and its original target. -/
def SameStageLocalizedInputs.RestrictionResult
    {K Ω : Type u} [Field K] [Field Ω] [IsAlgClosed Ω]
    (G : SameStageLocalizedInputs K Ω) (P : PresheafWithTransfers.{v} K) : Prop :=
  ∀ (Big : BigEtaleSite.{u})
    (_hX : Big.Contains
      (LocalizedRestriction.localizedRefinement G.tail G.q G.p G.s G.hs G.tGood).left)
    (_i₀ : SmallEtaleNeighborhood
      (LocalizedRestriction.localizedRefinement G.tail G.q G.p G.s G.hs G.tGood)
      (LocalizedRestriction.localizedRefinementPoint G.tail G.q G.p G.s G.hs G.tGood
        G.ξ G.η G.hξ G.ηV G.hη))
    (n : ℕ)
    (_hn : ∀ (V : SmoothSite (Spec (.of K)))
      (z : PresheafWithTransfers.sections P ((Cor.graphFunctor K).obj V)), (n + 1) • z = 0)
    (_hnK : IsUnit ((n + 1 : ℕ) : K)),
    let it := Scheme.EtaleChart.LocalizedRetainedLift.inclusion G.q.left G.p.left
      (QuadraticLocalized.scalar G.tGood) G.i (G.j ≫ G.fN) G.hi G.j G.fN rfl
    let ft := Scheme.EtaleChart.LocalizedRetainedLift.retainedProjection
      (QuadraticLocalized.scalar G.tGood) G.j G.fN
    let hit := Scheme.EtaleChart.LocalizedRetainedLift.inclusion_structure
      G.q.left G.p.left (QuadraticLocalized.scalar G.tGood)
      G.i (G.j ≫ G.fN) G.hi G.j G.fN rfl
    let tt := pullback.snd (QuadraticLocalized.toOriginal G.tGood G.fN) G.j ≫ G.targetU
    ∃ (htt : tt ≫ G.T.hom = ft ≫ (QuadraticLocalized.scalar G.tGood ≫ G.tail))
      (Anew : EtaleNeighborhood
        (LocalizedRestriction.localizedRefinement G.tail G.q G.p G.s G.hs G.tGood)
        (LocalizedRestriction.localizedRefinementPoint G.tail G.q G.p G.s G.hs G.tGood
          G.ξ G.η G.hξ G.ηV G.hη).hom),
      ((PresheafWithTransfers.toPresheaf K).obj P).map
        (etaleNeighborhoodHom _ _ Anew ≫
          OriginalFixed.originalTarget
            (LocalizedRestriction.localizedChart G.tail G.q G.p G.tGood)
            (LocalizedRestriction.localizedProjection G.tail G.p G.tGood)
            (LocalizedRestriction.localizedSection G.tail G.p G.s G.hs G.tGood)
            it ft hit tt htt).op =
      ((PresheafWithTransfers.toPresheaf K).obj P).map
        (etaleNeighborhoodHom _ _ Anew ≫
          OriginalFixed.retractTarget
            (LocalizedRestriction.localizedChart G.tail G.q G.p G.tGood)
            (LocalizedRestriction.localizedProjection G.tail G.p G.tGood)
            (LocalizedRestriction.localizedSection G.tail G.p G.s G.hs G.tGood)
            it ft hit tt htt).op

/-- The existing localized consumer applied to the stored original witnesses. -/
theorem SameStageLocalizedInputs.restrictionResult
    {K Ω : Type u} [Field K] [Field Ω] [IsAlgClosed Ω]
    (G : SameStageLocalizedInputs K Ω) (P : PresheafWithTransfers.{v} K)
    (hP : PresheafWithTransfers.IsA1Invariant P) : G.RestrictionResult P := by
  intro Big hX i₀ n hn hnK
  exact LocalizedRestriction.exists_localized_chart_restriction
    G.tail G.q G.p G.s G.hs G.tGood G.ξ G.η G.hξ G.ηV G.hη P hP
    G.j G.fN G.i G.hi G.d G.hd G.targetU G.hTarget G.π G.hπ G.aU G.haU G.hjπ
    G.eChart G.aE G.haE G.heπ G.ζ G.hζ Big hX i₀ n hn hnK

/-- Execute S1 on the selected geometry and use the genuinely lower structural
isomorphism to produce an original preimage. The remaining induction must supply
that lower isomorphism for the polynomial tail, not assume this conclusion. -/
theorem SameStageLocalizedInputs.exists_original_preimage_of_lower_iso
    {K Ω : Type u} [Field K] [Field Ω] [IsAlgClosed Ω]
    (G : SameStageLocalizedInputs K Ω) (P : PresheafWithTransfers.{u + 1} K)
    (hP : PresheafWithTransfers.IsA1Invariant P)
    (n : ℕ)
    (hn : ∀ (V : SmoothSite (Spec (.of K)))
      (z : PresheafWithTransfers.sections P ((Cor.graphFunctor K).obj V)), (n + 1) • z = 0)
    (hnK : IsUnit ((n + 1 : ℕ) : K))
    [hLowerIso : IsIso (etaleNeighborhoodValuePullback G.tailToBase G.originalMark_base.symm
      ((PresheafWithTransfers.toPresheaf K).obj P))]
    (b : ((PresheafWithTransfers.toPresheaf K).obj P).obj (op G.T)) :
    ∃ z : etaleNeighborhoodValue (SmoothSite.base (Spec (.of K)))
        (G.originalMark ≫ G.T.hom) ((PresheafWithTransfers.toPresheaf K).obj P),
      etaleNeighborhoodValuePullback G.targetToBase (ξ := G.originalMark) rfl
          ((PresheafWithTransfers.toPresheaf K).obj P) z =
        toEtaleNeighborhoodValueFromObject G.T G.originalMark
          ((PresheafWithTransfers.toPresheaf K).obj P) b := by
  classical
  let X := LocalizedRestriction.localizedRefinement G.tail G.q G.p G.s G.hs G.tGood
  let x := LocalizedRestriction.localizedRefinementPoint G.tail G.q G.p G.s G.hs G.tGood
    G.ξ G.η G.hξ G.ηV G.hη
  let Big := BigEtaleSite.containing X.left
  have hX : Big.Contains X.left := BigEtaleSite.contains_containing X.left
  let i₀ : SmallEtaleNeighborhood X x :=
    Classical.choice (IsCofiltered.nonempty (C := SmallEtaleNeighborhood X x))
  have hEq := G.restrictionResult P hP Big hX i₀ n hn hnK
  obtain ⟨z, hz⟩ := @OpenBaseChange.exists_original_preimage_of_nested_retained_restriction
    (Spec (.of K)) inferInstance G.A (SmoothSite.mk G.tail) G.Z G.T
    (base (Spec (.of K))) G.affineA
    (inferInstanceAs (IsAffine (Spec (.of G.R)))) G.affineZ inferInstance
    G.q G.etaleQ G.p G.smoothP G.s G.hs
    (Spec (.of (Localization.Away G.tGood))) inferInstance
    (QuadraticLocalized.scalar G.tGood)
    (inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap G.R (Localization.Away G.tGood))))))
    Ω inferInstance inferInstance G.ξ G.η G.hξ G.ηV G.hη
    G.tailToBase (G.originalMark ≫ G.T.hom) G.originalMark_base.symm
    ((PresheafWithTransfers.toPresheaf K).obj P) hLowerIso
    G.U G.N G.i (G.j ≫ G.fN) G.hi G.j G.fN rfl G.targetU G.hTarget b hEq
  exact ⟨z, G.original_preimage_of_lower_preimage
    ((PresheafWithTransfers.toPresheaf K).obj P) b z hz⟩

end QuadraticIncidence.InfinityChart
