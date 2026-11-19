/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphLiftCycle

/-!
# Relative lifts of graph correspondences

The native relative graph lift of a graph is the graph retaining its source coordinate.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
namespace AlgebraicGeometry.Cor.RelativeGraph
variable (k : Type u) [Field k]
variable {U Y : SmoothSite (Spec (CommRingCat.of k))} (f : U ⟶ Y)

/-- Retaining the source coordinate commutes with the literal graph map. -/
theorem graphMap_ambientLift :
    correspondenceGraphMap U.hom Y.hom f.left (MorphismProperty.Over.w f) ≫
      ambientLift k U Y =
    correspondenceGraphMap U.hom (SmoothSite.product U Y).hom
      (SmoothSite.productLift (𝟙 U) f).left
      (MorphismProperty.Over.w (SmoothSite.productLift (𝟙 U) f)) := by
  apply pullback.hom_ext
  · simp only [SmoothSite.product_hom, Category.assoc, ambientLift_fst, correspondenceGraphMap_fst]
  · simp only [SmoothSite.product_hom, Category.assoc, ambientLift_snd,
      correspondenceGraphMap_snd]
    apply pullback.hom_ext
    · simp [SmoothSite.productLift, correspondenceGraphMap_fst]
    · simp [SmoothSite.productLift, correspondenceGraphMap_snd]

/-- The actual additive relative lift takes the graph of `f` to the graph of `(id,f)`. -/
theorem relativeGraphLift_graph :
    relativeGraphLift k U Y ((graphFunctor k).map f) =
      (graphFunctor k).map (SmoothSite.productLift (𝟙 U) f) := by
  classical
  change relativeGraphLift k U Y
    (graphCorrespondenceOfComponents U.hom Y.hom f.left
      (MorphismProperty.Over.w f) (finite_genericPoints k (Cor.mk U))) =
    graphCorrespondenceOfComponents U.hom (SmoothSite.product U Y).hom
      (SmoothSite.productLift (𝟙 U) f).left
      (MorphismProperty.Over.w (SmoothSite.productLift (𝟙 U) f))
      (finite_genericPoints k (Cor.mk U))
  rw [graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence,
    graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence, map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [relativeGraphLift_single, one_smul]
  apply Subtype.ext
  change Function.locallyFinsuppWithin.single _ (1 : ℤ) =
    Function.locallyFinsuppWithin.single _ (1 : ℤ)
  congr 1
  exact congrArg (fun g => g x.val) (graphMap_ambientLift k f)
end AlgebraicGeometry.Cor.RelativeGraph
