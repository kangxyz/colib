/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.GraphProduct
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedSourceChange

/-!
# Changing the first parameter of the original finite product

The finite second-factor map and both compactification graphs use the same
literal first-factor change. This retains the full graph kernels.

Adapted from `OriginalNormParameterChart.lean` under
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Norm` at
a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- Changing the first parameter of a second-factor map forms the literal
Cartesian square of the original products. -/
theorem retainedProductInclusion_sourceChange_isPullback {S Y K C P : Scheme.{u}}
    (b : Y ⟶ S) (b' : K ⟶ S) (α : K ⟶ Y) (hα : α ≫ b = b')
    (π : P ⟶ S) (f : C ⟶ P) :
    IsPullback (retainedSourceChange b b' (f ≫ π) α hα)
      (retainedProductInclusion b' π f) (retainedProductInclusion b π f)
      (retainedSourceChange b b' π α hα) := by
  have houter : IsPullback (retainedSourceChange b b' (f ≫ π) α hα)
      (retainedProductInclusion b' π f ≫ pullback.fst b' π)
      (retainedProductInclusion b π f ≫ pullback.fst b π) α := by
    simp only [retainedProductInclusion_fst]
    exact retainedSourceChange_isPullback b b' (f ≫ π) α hα
  refine houter.of_bot ?_ (retainedSourceChange_isPullback b b' π α hα)
  apply pullback.hom_ext <;> simp only [Category.assoc, retainedProductInclusion_fst,
    retainedProductInclusion_fst_assoc, retainedProductInclusion_snd,
    retainedSourceChange_fst, retainedSourceChange_snd, retainedSourceChange_snd_assoc]

/-- The graph of the original target map pulled back to a changed parameter
is the graph of the actual composite. -/
theorem relativeGraph_sourceChange_isPullback {S Y K P : Scheme.{u}}
    (b : Y ⟶ S) (b' : K ⟶ S) (α : K ⟶ Y) (hα : α ≫ b = b')
    (π : P ⟶ S) (j : Y ⟶ P) (hj : j ≫ π = b) :
    IsPullback α
      (relativeGraph b' π (α ≫ j) (by rw [Category.assoc, hj, hα]))
      (relativeGraph b π j hj) (retainedSourceChange b b' π α hα) := by
  have houter : IsPullback α
      (relativeGraph b' π (α ≫ j) (by rw [Category.assoc, hj, hα]) ≫ pullback.fst b' π)
      (relativeGraph b π j hj ≫ pullback.fst b π) α := by
    simpa only [relativeGraph_fst] using (IsPullback.id_vert α)
  refine houter.of_bot ?_ (retainedSourceChange_isPullback b b' π α hα)
  apply pullback.hom_ext <;> simp only [Category.assoc, relativeGraph_fst,
    relativeGraph_fst_assoc, relativeGraph_snd, retainedSourceChange_fst, retainedSourceChange_snd,
    Category.comp_id]

/-- Changing the first parameter and restricting the second factor commute
on the actual product. -/
theorem retainedSourceChange_comp_retainedProductInclusion {S Y K P A : Scheme.{u}}
    (b : Y ⟶ S) (b' : K ⟶ S) (α : K ⟶ Y) (hα : α ≫ b = b')
    (π : P ⟶ S) (a : A ⟶ P) :
    retainedSourceChange b b' (a ≫ π) α hα ≫ retainedProductInclusion b π a =
      retainedProductInclusion b' π a ≫ retainedSourceChange b b' π α hα := by
  exact (retainedProductInclusion_sourceChange_isPullback b b' α hα π a).w

/-- The retained product contains a point precisely when its original second
projection lies in the image of the retained second factor. -/
theorem mem_range_retainedProductInclusion {S Y P A : Scheme.{u}}
    (b : Y ⟶ S) (π : P ⟶ S) (a : A ⟶ P) (x : (pullback b π : Scheme.{u})) :
    x ∈ Set.range (retainedProductInclusion b π a) ↔
      pullback.snd b π x ∈ Set.range a := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨pullback.snd b (a ≫ π) y,
      congrArg (fun f ↦ f y) (retainedProductInclusion_snd b π a).symm⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback
      (retainedProductInclusion_isPullback b π a) y x hy
    exact ⟨z, hz⟩

/-- The original full zero support is still in the original retained second
factor after an actual change of the first parameter. -/
theorem wholeSupport_sourceChange {S Y K P A : Scheme.{u}}
    (b : Y ⟶ S) (b' : K ⟶ S) (α : K ⟶ Y) (hα : α ≫ b = b')
    (π : P ⟶ S) (a : A ⟶ P) (I : (pullback b π).IdealSheafData)
    (hI : Set.range I.subschemeι ⊆ Set.range (retainedProductInclusion b π a)) :
    Set.range (I.comap (retainedSourceChange b b' π α hα)).subschemeι ⊆
      Set.range (retainedProductInclusion b' π a) := by
  let ρ := retainedSourceChange b b' π α hα
  intro x hx
  rw [(I.comap ρ).range_subschemeι, IdealSheafData.support_comap] at hx
  have hρ : ρ x ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact hx
  apply (mem_range_retainedProductInclusion b' π a x).2
  have hy := (mem_range_retainedProductInclusion b π a (ρ x)).1 (hI hρ)
  rwa [← Hom.comp_apply, retainedSourceChange_snd] at hy

end AlgebraicGeometry.Scheme.RelativeCurvePencil
