/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
/- Source-only candidate: actual section ranges in actual retained pullbacks. -/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenRetained
/-! # The original sections remain in the actual retained opens -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.SmoothSite
private theorem section_range_pullback {P X Y T A : Scheme.{u}}
    {j' : P ⟶ X} {v : P ⟶ Y} {f : X ⟶ T} {j : Y ⟶ T}
    (hp : IsPullback j' v f j) (σ : A ⟶ X)
    (hσ : ∀ x : A, f (σ x) ∈ Set.range j) : Set.range σ ⊆ Set.range j' := by
  have hr : Set.range j' = f ⁻¹' Set.range j := by
    rw [← hp.isoPullback_hom_fst]
    change Set.range (pullback.fst f j ∘ hp.isoPullback.hom) = _
    rw [Set.range_comp, hp.isoPullback.hom.surjective.range_eq,
      Set.image_univ, Scheme.Pullback.range_fst]
  rintro _ ⟨x, rfl⟩
  rw [hr]
  exact hσ x

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
  (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
  {V : Scheme.{u}} (j : V ⟶ U.toScheme)
  (σ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
  (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
  (hσj : Set.range σ ⊆ Set.range j)

include hσj

theorem etaleStageOpenSection_range_retained (a : Over i) :
    Set.range (etaleStageOpenSection X s p i U σ hσ a) ⊆
      Set.range ((etaleStageOpenBoundaryMap X s p i U j).app a) := by
  apply section_range_pullback (etaleStageOpenBoundaryMap_isPullback X s p i U j a)
  intro x
  have hx := congrArg (fun t => t x) (etaleStageOpenSection_snd X s p i U σ hσ a)
  change (pullback.snd ((etaleCurveDiagram X s p).map a.hom) U.ι)
    (etaleStageOpenSection X s p i U σ hσ a x) ∈ Set.range j
  exact (congrArg (fun y => y ∈ Set.range j) hx).mpr (hσj ⟨_, rfl⟩)

theorem etaleStageOpenLimitSection_range_retained (B : BigEtaleSite.{u})
    (hX : B.Contains X.left) :
    Set.range (etaleStageOpenLimitSection X s p i U B hX σ hσ) ⊆
      Set.range (etaleStageOpenBoundaryLimitMap X s p i U j B hX) := by
  apply section_range_pullback (etaleStageOpenBoundaryLimitMap_isPullback X s p i U j B hX)
  intro x
  have hx := congrArg (fun t => t x)
    (etaleStageOpenLimitSection_snd X s p i U B hX σ hσ)
  change (pullback.snd ((etaleCurveCone X B hX s p).π.app i) U.ι)
    (etaleStageOpenLimitSection X s p i U B hX σ hσ x) ∈ Set.range j
  exact (congrArg (fun y => y ∈ Set.range j) hx).mpr (hσj ⟨_, rfl⟩)
end AlgebraicGeometry.Scheme.SmoothSite
