/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenSections

/-! # Original sections on the actual component limit

The section on the component-model limit is constructed from the same fixed-stage
section. Its compatibility with every stage is a consequence of native pullback
uniqueness and the original cone equations.
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

/-- The actual component-model limit structure over the original strict-local base. -/
def etaleStageOpenLimitStructure : (etaleStageOpenCone X s p i U B hX).pt ⟶
    (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).pt :=
  pullback.fst ((etaleCurveCone X B hX s p).π.app i) U.ι ≫
    pullback.fst (strictHenselizationToBase B X.left hX s) p

/-- The component-model limit is Cartesian over the fixed finite-stage component. -/
theorem etaleStageOpenLimitStructure_isPullback :
    IsPullback (pullback.snd ((etaleCurveCone X B hX s p).π.app i) U.ι)
      (etaleStageOpenLimitStructure X s p i U B hX)
      (U.ι ≫ (etaleCurveStructure X s p).app i)
      ((smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app i) :=
  (IsPullback.of_hasPullback ((etaleCurveCone X B hX s p).π.app i) U.ι).flip.paste_vert
    (etaleCurveCone_isPullback X B hX s p i)

/-- The actual component cone leg preserves the fixed-stage component projection. -/
@[simp, reassoc] theorem etaleStageOpenCone_π_snd (a : Over i) :
    (etaleStageOpenCone X s p i U B hX).π.app a ≫
      pullback.snd ((etaleCurveDiagram X s p).map a.hom) U.ι =
    pullback.snd ((etaleCurveCone X B hX s p).π.app i) U.ι :=
  pullback.lift_snd _ _ _

/-- The actual component cone square commutes over the unchanged base cone. -/
theorem etaleStageOpenCone_structure_square (a : Over i) :
    (etaleStageOpenCone X s p i U B hX).π.app a ≫
      (etaleStageOpenStructure X s p i U).app a =
    etaleStageOpenLimitStructure X s p i U B hX ≫
      (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app a.left := by
  change pullback.lift _ _ _ ≫
    (pullback.fst ((etaleCurveDiagram X s p).map a.hom) U.ι ≫
      (etaleCurveStructure X s p).app a.left) = _
  simp only [pullback.lift_fst_assoc, Category.assoc, etaleStageOpenLimitStructure]
  exact congrArg (fun f =>
    pullback.fst ((etaleCurveCone X B hX s p).π.app i) U.ι ≫ f)
      (etaleCurveCone_π_fst X B hX s p a.left)

/-- The actual limit-to-stage component square is Cartesian. -/
theorem etaleStageOpenCone_isPullback (a : Over i) :
    IsPullback ((etaleStageOpenCone X s p i U B hX).π.app a)
      (etaleStageOpenLimitStructure X s p i U B hX)
      ((etaleStageOpenStructure X s p i U).app a)
      ((smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app a.left) := by
  refine IsPullback.of_right ?_ (etaleStageOpenCone_structure_square X s p i U B hX a)
    (etaleStageOpenStructure_isPullback X s p i U a)
  rw [etaleStageOpenCone_π_snd,
    (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).w a.hom]
  exact etaleStageOpenLimitStructure_isPullback X s p i U B hX

variable (σ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
  (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)

/-- The original fixed-stage section lifted to the actual component-model limit. -/
def etaleStageOpenLimitSection :
    (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).pt ⟶
      (etaleStageOpenCone X s p i U B hX).pt :=
  (etaleStageOpenLimitStructure_isPullback X s p i U B hX).lift
    ((smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app i ≫ σ) (𝟙 _)
    (by simp only [Category.assoc, hσ, Category.comp_id, Category.id_comp])

@[simp, reassoc] theorem etaleStageOpenLimitSection_snd :
    etaleStageOpenLimitSection X s p i U B hX σ hσ ≫
      pullback.snd ((etaleCurveCone X B hX s p).π.app i) U.ι =
    (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app i ≫ σ :=
  IsPullback.lift_fst _ _ _ _

@[simp, reassoc] theorem etaleStageOpenLimitSection_structure :
    etaleStageOpenLimitSection X s p i U B hX σ hσ ≫
      etaleStageOpenLimitStructure X s p i U B hX = 𝟙 _ :=
  IsPullback.lift_snd _ _ _ _

/-- The constructed original limit section commutes with each actual stage section. -/
theorem etaleStageOpenLimitSection_comp (a : Over i) :
    etaleStageOpenLimitSection X s p i U B hX σ hσ ≫
      (etaleStageOpenCone X s p i U B hX).π.app a =
    (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app a.left ≫
      etaleStageOpenSection X s p i U σ hσ a := by
  apply (etaleStageOpenStructure_isPullback X s p i U a).hom_ext
  · simp only [Category.assoc, etaleStageOpenCone_π_snd,
      etaleStageOpenLimitSection_snd, etaleStageOpenSection_snd]
    rw [← Category.assoc, (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).w a.hom]
  · rw [Category.assoc, etaleStageOpenCone_structure_square]
    simp only [Category.assoc, etaleStageOpenLimitSection_structure_assoc,
      etaleStageOpenSection_structure, Category.comp_id]

/-- The original limit section and stage section give a Cartesian full-kernel
comparison, without any assumed section-compatibility equation. -/
theorem etaleStageOpenLimitSection_isPullback (a : Over i) :
    IsPullback (etaleStageOpenLimitSection X s p i U B hX σ hσ)
      ((smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app a.left)
      ((etaleStageOpenCone X s p i U B hX).π.app a)
      (etaleStageOpenSection X s p i U σ hσ a) :=
  Scheme.isPullback_section_of_isPullback
    ((etaleStageOpenCone X s p i U B hX).π.app a)
    (etaleStageOpenLimitStructure X s p i U B hX)
    ((etaleStageOpenStructure X s p i U).app a)
    ((smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app a.left)
    (etaleStageOpenCone_isPullback X s p i U B hX a)
    (etaleStageOpenLimitSection X s p i U B hX σ hσ)
    (etaleStageOpenSection X s p i U σ hσ a)
    (etaleStageOpenLimitSection_structure X s p i U B hX σ hσ)
    (etaleStageOpenSection_structure X s p i U σ hσ a)
    (etaleStageOpenLimitSection_comp X s p i U B hX σ hσ a)

end AlgebraicGeometry.Scheme.SmoothSite
