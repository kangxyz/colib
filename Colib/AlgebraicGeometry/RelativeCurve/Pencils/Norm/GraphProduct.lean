/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.MarkedGraphGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedBoundaryCover
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The finite product map of the original graphs

The two actual compactification graphs form a closed triangle over a finite
map. Restricting the triangle to a chart preserves the two exact kernel
ideals and their scheme structures.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Graph/Frames/OriginalTriangle.lean`
and `Morphisms/Finite/Norm/OpenGraphTriangle.lean` under the same
`Motivic/Aglib/AlgebraicGeometry` at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S P C X Y : Scheme.{u}} (π : P ⟶ S) (f : C ⟶ P) (j : Y ⟶ C)

/-- The second-factor map retains finiteness by its actual Cartesian square. -/
instance retainedProductInclusion_finite {B : Scheme.{u}} (b : B ⟶ S) [IsFinite f] :
    IsFinite (retainedProductInclusion b π f) :=
  MorphismProperty.of_isPullback (retainedProductInclusion_isPullback b π f) inferInstance

/-- The original finite morphism in the second factor of the relative product. -/
abbrev graphProductMap : pullback (j ≫ f ≫ π) (f ≫ π) ⟶ pullback (j ≫ f ≫ π) π :=
  retainedProductInclusion (j ≫ f ≫ π) π f

@[reassoc]
theorem graphProductMap_fst :
    graphProductMap π f j ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [graphProductMap]

@[reassoc]
theorem graphProductMap_snd :
    graphProductMap π f j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ f := by
  simp [graphProductMap]

/-- The graph of the original map from the retained source into the target. -/
abbrev targetNormGraph : Y ⟶ pullback (j ≫ f ≫ π) π :=
  relativeGraph (j ≫ f ≫ π) π (j ≫ f) (Category.assoc j f π)

@[reassoc (attr := simp)]
theorem compactificationGraph_comp_graphProductMap :
    compactificationGraph (f ≫ π) j ≫ graphProductMap π f j = targetNormGraph π f j := by
  apply pullback.hom_ext <;> simp [compactificationGraph, targetNormGraph]

variable (jA : X ⟶ P) (p : Y ⟶ X) (h : j ≫ f = p ≫ jA)

/-- The original change of parameter from the retained source to the target. -/
def graphTargetParameterMap : pullback (j ≫ f ≫ π) π ⟶ pullback (jA ≫ π) π :=
  pullback.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _)
    (by rw [Category.assoc, ← Category.assoc p, ← h, Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
theorem graphTargetParameterMap_fst :
    graphTargetParameterMap π f j jA p h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graphTargetParameterMap_snd :
    graphTargetParameterMap π f j jA p h ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The target graph and its changed parameter form the original Cartesian square. -/
theorem targetNormGraph_isPullback :
    IsPullback p (targetNormGraph π f j) (compactificationGraph π jA)
      (graphTargetParameterMap π f j jA p h) where
  w := by
    apply pullback.hom_ext
    · simp [compactificationGraph, targetNormGraph]
    · simpa [compactificationGraph, targetNormGraph] using h.symm
  isLimit' := ⟨PullbackCone.isLimitAux' _ fun t ↦ by
    let v := t.snd ≫ pullback.fst (j ≫ f ≫ π) π
    have hv : v ≫ p = t.fst := by
      have e := congrArg (fun a ↦ a ≫ pullback.fst (jA ≫ π) π) t.condition
      simpa [v, compactificationGraph, Category.assoc] using e.symm
    have hw : v ≫ targetNormGraph π f j = t.snd := by
      apply pullback.hom_ext
      · simp [v, targetNormGraph]
      · calc
          (v ≫ targetNormGraph π f j) ≫ pullback.snd _ _ = (v ≫ p) ≫ jA := by
            simp [Category.assoc, targetNormGraph, h]
          _ = t.fst ≫ jA := by rw [hv]
          _ = t.snd ≫ pullback.snd _ _ := by
            have e := congrArg (fun a ↦ a ≫ pullback.snd (jA ≫ π) π) t.condition
            simpa [compactificationGraph, Category.assoc] using e
    refine ⟨v, hv, hw, ?_⟩
    intro a _ ha
    have e := congrArg (fun b ↦ b ≫ pullback.fst (j ≫ f ≫ π) π) ha
    simpa [v, targetNormGraph, Category.assoc] using e⟩

/-- The changed parameter retains exactly the target graph ideal. -/
theorem targetNormGraph_ker [IsSeparated π] :
    (targetNormGraph π f j).ker =
      (compactificationGraph π jA).ker.comap (graphTargetParameterMap π f j jA p h) :=
  ker_eq_comap_of_cartesian (targetNormGraph_isPullback π f j jA p h).flip

variable {W : Scheme.{u}} (w : W ⟶ pullback (j ≫ f ≫ π) π)

/-- Restriction of either graph to the same original target chart gives the
same domain, with its actual projection. -/
def graphNormChartDomainIso :
    pullback (compactificationGraph (f ≫ π) j) (pullback.fst (graphProductMap π f j) w) ≅
      pullback (targetNormGraph π f j) w :=
  pullbackRightPullbackFstIso (graphProductMap π f j) w (compactificationGraph (f ≫ π) j) ≪≫
    pullback.congrHom (compactificationGraph_comp_graphProductMap π f j) rfl

/-- The original restricted graphs form a triangle over the actual finite chart map. -/
theorem graphNormChart_triangle :
    pullback.snd (compactificationGraph (f ≫ π) j)
        (pullback.fst (graphProductMap π f j) w) ≫ pullback.snd (graphProductMap π f j) w =
      (graphNormChartDomainIso π f j w).hom ≫ pullback.snd (targetNormGraph π f j) w := by
  simp [graphNormChartDomainIso]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
