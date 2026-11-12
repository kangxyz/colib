/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenLimitSections

/-! # Identity with the original normal-component section

The original section is the native Cartesian base change of the specified stage
section, followed by the existing `liftToNormalComponent`. Its equality with the
component-model limit section is proved through the actual component inclusion.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
  (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
  (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
  [IsLocallyNoetherian (etaleCurveCone X B hX s p).pt]
  [IsNormal (etaleCurveCone X B hX s p).pt]
  (x : (etaleCurveCone X B hX s p).pt)
  (hpre : (etaleCurveCone X B hX s p).π.app i ⁻¹ᵁ U = normalComponentOpen x)

/-- The original component iso preserves its literal inclusion into the whole curve. -/
@[simp, reassoc] theorem etaleStageOpenConeNormalComponentIso_hom_ι :
    (etaleStageOpenConeNormalComponentIso X s p i U B hX x hpre).hom ≫
      (normalComponentOpen x).ι =
    pullback.fst ((etaleCurveCone X B hX s p).π.app i) U.ι := by
  simp only [etaleStageOpenConeNormalComponentIso, Iso.trans_hom, Category.assoc,
    Scheme.isoOfEq_hom_ι, etaleStageOpenConePreimageIso_hom_ι]

variable (σ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
  (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)

/-- The actual whole-curve base change of the original section already factored
through the chosen stage open. It is independent of the component-model limit. -/
def etaleStageOriginalBaseChangeSection :
    (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).pt ⟶
      (etaleCurveCone X B hX s p).pt :=
  (etaleCurveCone_isPullback X B hX s p i).lift
    ((smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app i ≫ σ ≫ U.ι)
    (𝟙 _) (by simp only [Category.assoc, hσ, Category.comp_id, Category.id_comp])

omit [IsLocallyNoetherian (etaleCurveCone X B hX s p).pt]
  [IsNormal (etaleCurveCone X B hX s p).pt] in
@[simp, reassoc] theorem etaleStageOriginalBaseChangeSection_stage :
    etaleStageOriginalBaseChangeSection X s p i U B hX σ hσ ≫
      (etaleCurveCone X B hX s p).π.app i =
    (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app i ≫ σ ≫ U.ι :=
  IsPullback.lift_fst _ _ _ _

omit [IsLocallyNoetherian (etaleCurveCone X B hX s p).pt]
  [IsNormal (etaleCurveCone X B hX s p).pt] in
@[simp, reassoc] theorem etaleStageOriginalBaseChangeSection_structure :
    etaleStageOriginalBaseChangeSection X s p i U B hX σ hσ ≫
      pullback.fst (strictHenselizationToBase B X.left hX s) p = 𝟙 _ :=
  IsPullback.lift_snd _ _ _ _

omit [IsLocallyNoetherian (etaleCurveCone X B hX s p).pt]
  [IsNormal (etaleCurveCone X B hX s p).pt] in
/-- The component-model section retains the actual whole-curve base-change section. -/
theorem etaleStageOpenLimitSection_original :
    etaleStageOpenLimitSection X s p i U B hX σ hσ ≫
      pullback.fst ((etaleCurveCone X B hX s p).π.app i) U.ι =
    etaleStageOriginalBaseChangeSection X s p i U B hX σ hσ := by
  apply (etaleCurveCone_isPullback X B hX s p i).hom_ext
  · rw [Category.assoc, pullback.condition, ← Category.assoc,
      etaleStageOpenLimitSection_snd, etaleStageOriginalBaseChangeSection_stage]
    exact Category.assoc _ _ _
  · rw [Category.assoc]
    change etaleStageOpenLimitSection X s p i U B hX σ hσ ≫
      etaleStageOpenLimitStructure X s p i U B hX = _
    rw [etaleStageOpenLimitSection_structure, etaleStageOriginalBaseChangeSection_structure]

include hpre in
/-- Membership of the original base-changed closed point is derived from the
original stage factorization and actual component-preimage equality. -/
theorem etaleStageOriginalBaseChangeSection_closedPoint_mem :
    etaleStageOriginalBaseChangeSection X s p i U B hX σ hσ
      (IsLocalRing.closedPoint ↥(etaleLocalRing B X.left hX s)) ∈ normalComponentOpen x := by
  rw [← hpre]
  change ((etaleCurveCone X B hX s p).π.app i)
    (etaleStageOriginalBaseChangeSection X s p i U B hX σ hσ
      (IsLocalRing.closedPoint ↥(etaleLocalRing B X.left hX s))) ∈ U
  have h := congrArg
    (fun f => f (IsLocalRing.closedPoint ↥(etaleLocalRing B X.left hX s)))
    (etaleStageOriginalBaseChangeSection_stage X s p i U B hX σ hσ)
  exact h.symm ▸ (σ ((smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app i
    (IsLocalRing.closedPoint ↥(etaleLocalRing B X.left hX s)))).property

/-- The constructed limit section is exactly the original normal-component lift,
not a replacement section with an assumed compatibility equation. -/
theorem etaleStageOpenLimitSection_eq_original_component :
    etaleStageOpenLimitSection X s p i U B hX σ hσ ≫
      (etaleStageOpenConeNormalComponentIso X s p i U B hX x hpre).hom =
    Scheme.liftToNormalComponent
      (etaleStageOriginalBaseChangeSection X s p i U B hX σ hσ) x
      (etaleStageOriginalBaseChangeSection_closedPoint_mem X s p i U B hX x hpre σ hσ) := by
  apply (cancel_mono (normalComponentOpen x).ι).mp
  rw [Category.assoc, etaleStageOpenConeNormalComponentIso_hom_ι,
    Scheme.liftToNormalComponent_ι]
  exact etaleStageOpenLimitSection_original X s p i U B hX σ hσ

end AlgebraicGeometry.Scheme.SmoothSite
