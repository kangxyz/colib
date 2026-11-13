/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.Components

/-!
# Signed correspondences from an integral source to its base

The first projection of `X ×[S] S` is an isomorphism. The component condition
on an actual admissible point forces its projection to be the unique generic
point of `X`. Thus every correspondence is its literal coefficient at the
structure graph times that graph. This uses the existing native cycle subgroup,
not a replacement free group or a chosen abstract rank-one object.

Implementation provenance: `motivic_source_a6805c4`,
`Motivic/AlgebraicGeometry/Correspondences/BaseChange/IntegralSource.lean:27-61`.
The source's integral closed generators are realized by their native generic
points. No field, smoothness, affine or Noetherian hypothesis is needed here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin

universe u

namespace Stacks.Chow

variable {S X : Scheme.{u}} [IsIntegral X] (f : X ⟶ S)

/-- The actual generic point of the graph of the structure morphism. -/
def structureGraphPoint : (pullback f (𝟙 S) : Scheme.{u}) :=
  correspondenceGraphMap f (𝟙 S) f (Category.comp_id f) (genericPoint X)

/-- The source coordinate of the structure graph is the original generic point. -/
@[simp]
theorem structureGraphPoint_fst :
    (pullback.fst f (𝟙 S)) (structureGraphPoint f) = genericPoint X := by
  change (correspondenceGraphMap f (𝟙 S) f (Category.comp_id f) ≫
    pullback.fst f (𝟙 S)) (genericPoint X) = _
  rw [correspondenceGraphMap_fst]
  rfl

/-- The structure graph point is an actual finite-correspondence point. -/
theorem isFiniteCorrespondencePoint_structureGraphPoint :
    IsFiniteCorrespondencePoint f (𝟙 S) (structureGraphPoint f) :=
  isFiniteCorrespondencePoint_graphMap f (𝟙 S) f (Category.comp_id f)
    ⟨genericPoint X, by simp only [genericPoints_eq_singleton, Set.mem_singleton_iff]⟩

/-- Every admissible support over the base is the actual structure graph support. -/
theorem eq_structureGraphPoint_of_isFiniteCorrespondencePoint
    (z : (pullback f (𝟙 S) : Scheme.{u})) (hz : IsFiniteCorrespondencePoint f (𝟙 S) z) :
    z = structureGraphPoint f := by
  let := isIntegral_integralComponentAt z
  let π := (integralComponentAt z).subschemeι ≫ pullback.fst f (𝟙 S)
  have hr : Set.range π = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using hz.2
  have hg : π (genericPoint (integralComponentAt z).subscheme) = genericPoint X := by
    refine IsGenericPoint.eq ?_ (genericPoint_spec X)
    simpa only [Set.image_univ, hr, closure_univ] using
      (genericPoint_spec (integralComponentAt z).subscheme).image π.continuous
  have hz' : (integralComponentAt z).subschemeι
      (genericPoint (integralComponentAt z).subscheme) = z :=
    genericPointOf_integralComponentAt z
  apply (Scheme.homeoOfIso (asIso (pullback.fst f (𝟙 S)))).injective
  change (pullback.fst f (𝟙 S)) z = (pullback.fst f (𝟙 S)) (structureGraphPoint f)
  rw [structureGraphPoint_fst]
  change (pullback.fst f (𝟙 S))
    ((integralComponentAt z).subschemeι
      (genericPoint (integralComponentAt z).subscheme)) = genericPoint X at hg
  rwa [hz'] at hg

/-- The structure graph as the actual native prime correspondence. -/
def structureGraphCorrespondence : finiteCorrespondences f (𝟙 S) := by
  classical
  exact ⟨single (structureGraphPoint f) 1,
    single_mem_finiteCorrespondences f (𝟙 S) _
      (isFiniteCorrespondencePoint_structureGraphPoint f) 1⟩

/-- Coefficient extraction at the literal structure graph point. -/
def structureCorrespondenceCoeff : finiteCorrespondences f (𝟙 S) →+ ℤ where
  toFun a := a.val (structureGraphPoint f)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The actual structure graph has integer coefficient one. -/
@[simp]
theorem structureCorrespondenceCoeff_graph :
    structureCorrespondenceCoeff f (structureGraphCorrespondence f) = 1 := by
  classical
  simp [structureCorrespondenceCoeff, structureGraphCorrespondence]

/-- Every signed correspondence to the base retains exactly its original coefficient. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/BaseChange/IntegralSource.lean:47-53"
  "adaptation" "The actual native signed cycle is its graph coefficient times the structure graph"]
theorem eq_coeff_zsmul_structureGraph (a : finiteCorrespondences f (𝟙 S)) :
    a = structureCorrespondenceCoeff f a • structureGraphCorrespondence f := by
  classical
  apply Subtype.ext
  ext z
  change a.val z = structureCorrespondenceCoeff f a •
    (single (structureGraphPoint f) (1 : ℤ)) z
  by_cases hz : z = structureGraphPoint f
  · subst z
    simp [structureCorrespondenceCoeff]
  · have ha : a.val z = 0 := by
      by_contra h
      exact hz (eq_structureGraphPoint_of_isFiniteCorrespondencePoint f z (a.property.2 z h))
    simp [single_apply, hz, ha]

/-- The graph sum used by the correspondence category is this same prime cycle. -/
theorem graphCorrespondenceOfComponents_structure
    (hX : (genericPoints X).Finite) :
    graphCorrespondenceOfComponents f (𝟙 S) f (Category.comp_id f) hX =
      structureGraphCorrespondence f := by
  classical
  have hfin : hX.toFinset = {genericPoint X} := by
    ext x
    simp only [Set.Finite.mem_toFinset, genericPoints_eq_singleton,
      Set.mem_singleton_iff, Finset.mem_singleton]
  apply Subtype.ext
  rw [graphCorrespondenceOfComponents_coe, hfin]
  simp [structureGraphCorrespondence, structureGraphPoint]

/-- The coefficient and actual structure graph identify this correspondence group with `ℤ`. -/
def structureCorrespondenceEquiv : finiteCorrespondences f (𝟙 S) ≃+ ℤ where
  toFun := structureCorrespondenceCoeff f
  invFun n := n • structureGraphCorrespondence f
  left_inv a := (eq_coeff_zsmul_structureGraph f a).symm
  right_inv n := by
    rw [map_zsmul, structureCorrespondenceCoeff_graph]
    exact Int.mul_one n
  map_add' := (structureCorrespondenceCoeff f).map_add

end Stacks.Chow
