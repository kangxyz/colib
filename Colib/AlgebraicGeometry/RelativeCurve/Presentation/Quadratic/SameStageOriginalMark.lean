/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.SameStageLocalizedInputs
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartOriginalFixedInputs
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodEtalePreimage

/-! # The original marked target of the stored same-stage chart -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.SmoothSite.EtaleChart
universe u
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

local instance {K : Type u} [Field K] : IsAffine (SmoothSite.base (Spec (.of K))).left :=
  inferInstanceAs (IsAffine (Spec (.of K)))

variable {K Ω : Type u} [Field K] [Field Ω] (G : SameStageLocalizedInputs K Ω)

/-- The actual retained map gives a morphism to the original target on the K-site. -/
def SameStageLocalizedInputs.originalChart : G.A ⟶ G.T :=
  OriginalFixed.chartTarget G.q G.p G.i (G.j ≫ G.fN) G.hi G.targetU G.hTarget

/-- This chart preserves the stored original marking as a scheme morphism. -/
theorem SameStageLocalizedInputs.originalChart_mark :
    G.ξ ≫ G.originalChart.left = G.originalMark := G.originalMark_eq

/-- The original and lower markings have the same map to the unchanged ground field. -/
theorem SameStageLocalizedInputs.originalMark_base :
    G.originalMark ≫ G.T.hom = G.η ≫ G.tail := by
  rw [← G.originalChart_mark, Category.assoc, MorphismProperty.Over.w]
  have hw : (G.q ≫ G.p).left ≫ G.tail = G.A.hom :=
    MorphismProperty.Over.w (G.q ≫ G.p)
  calc
    _ = G.ξ ≫ ((G.q ≫ G.p).left ≫ G.tail) := congrArg (fun f => G.ξ ≫ f) hw.symm
    _ = (G.ξ ≫ (G.q ≫ G.p).left) ≫ G.tail := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫ G.tail)
      (chartMark_base G.q G.p G.s G.ξ G.η G.hξ G.hs)

/-- The original-target map is the actual finite-separable tensor chart, hence étale. -/
instance SameStageLocalizedInputs.originalChart_etale : Etale G.originalChart.left :=
  G.originalChartEtale

/-- The original target's structural morphism in the unchanged K-site. -/
def SameStageLocalizedInputs.targetToBase : G.T ⟶ SmoothSite.base (Spec (.of K)) :=
  homMk G.T.hom (by change G.T.hom ≫ 𝟙 _ = G.T.hom; simp)

/-- The lower polynomial tail's structural morphism in the same K-site. -/
def SameStageLocalizedInputs.tailToBase :
    SmoothSite.mk G.tail ⟶ SmoothSite.base (Spec (.of K)) :=
  homMk G.tail (by change G.tail ≫ 𝟙 _ = G.tail; simp)

/-- The actual original chart and lower projection have the same structure map. -/
theorem SameStageLocalizedInputs.originalChart_base_square :
    G.originalChart ≫ G.targetToBase = (G.q ≫ G.p) ≫ G.tailToBase := by
  apply MorphismProperty.Over.Hom.ext
  change G.originalChart.left ≫ G.T.hom = (G.q ≫ G.p).left ≫ G.tail
  exact (MorphismProperty.Over.w G.originalChart).trans
    (MorphismProperty.Over.w (G.q ≫ G.p)).symm

/-- The lower total map recovers the original base marking. -/
theorem SameStageLocalizedInputs.lower_base_mark :
    G.ξ ≫ ((G.q ≫ G.p) ≫ G.tailToBase).left = G.originalMark ≫ G.T.hom := by
  change G.ξ ≫ ((G.q ≫ G.p).left ≫ G.tail) = G.originalMark ≫ G.T.hom
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ G.tail)
      (chartMark_base G.q G.p G.s G.ξ G.η G.hξ G.hs)).trans G.originalMark_base.symm)

/-- An actual lower preimage reflects back to the original representative.
The supplied lower preimage is the remaining induction obligation, not a new axiom. -/
theorem SameStageLocalizedInputs.original_preimage_of_lower_preimage
    [IsSepClosed Ω] (F : (SmoothSite (Spec (.of K)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (b : F.obj (op G.T))
    (z : etaleNeighborhoodValue (SmoothSite.base (Spec (.of K)))
      (G.originalMark ≫ G.T.hom) F)
    (hz : etaleNeighborhoodValuePullback ((G.q ≫ G.p) ≫ G.tailToBase)
      G.lower_base_mark F z =
      toEtaleNeighborhoodValueFromObject G.A G.ξ F (F.map G.originalChart.op b)) :
    etaleNeighborhoodValuePullback G.targetToBase (ξ := G.originalMark) rfl F z =
      toEtaleNeighborhoodValueFromObject G.T G.originalMark F b := by
  simp only [← G.originalChart_base_square] at hz
  exact original_preimage_of_etale_chart_preimage G.originalChart G.targetToBase
    G.ξ G.originalMark (G.originalMark ≫ G.T.hom) G.originalChart_mark rfl F b z hz

end QuadraticIncidence.InfinityChart
