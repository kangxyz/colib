/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineProjModel
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The literal polynomial chart and infinity in the native relative projective line

The native gluing-to-projective-space isomorphism is over the original ring.
Infinity is the actual zero section in the other chart, including all nilpotents
of the base ring. No point-set replacement is used to define this closed scheme.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine
variable (R : Type u) [CommRing R]

/-- The original polynomial coordinate in the native projective-space model. -/
def chart : Spec (.of (Polynomial R)) ⟶ projectiveSpaceOverRing 1 (.of R) :=
  projectiveLineXChart R ≫ (projectiveLineIsoProjectiveSpaceOver R).hom

instance : IsOpenImmersion (chart R) := by unfold chart; infer_instance

@[reassoc (attr := simp)]
theorem chart_projection :
    chart R ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) := by
  rw [chart, Category.assoc, projectiveLineIsoProjectiveSpaceOver_hom_fst,
    projectiveLineXChart_comp_structureMorphism]

/-- The full base scheme, embedded as the zero coordinate of the second chart. -/
def infinity : Spec (.of R) ⟶ projectiveSpaceOverRing 1 (.of R) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
    projectiveLineYChart R ≫ (projectiveLineIsoProjectiveSpaceOver R).hom

@[reassoc (attr := simp)]
theorem infinity_projection :
    infinity R ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) = 𝟙 _ := by
  simp only [infinity, Category.assoc, projectiveLineIsoProjectiveSpaceOver_hom_fst,
    projectiveLineYChart_comp_structureMorphism]
  change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  exact Polynomial.eval_C

instance : IsClosedImmersion (infinity R) := by
  have : IsClosedImmersion
      (infinity R ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))) := by
    rw [infinity_projection]; infer_instance
  exact IsClosedImmersion.of_comp _ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))

/-- The image of evaluation at zero is the entire coordinate-zero locus. -/
theorem mem_range_evalZero_iff (y : Spec (.of (Polynomial R))) :
    y ∈ Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ↔
      Polynomial.X ∈ y.asIdeal := by
  change y ∈ Set.range (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : R))) ↔ _
  rw [range_comap_of_surjective R (Polynomial.evalRingHom (0 : R))
    (Polynomial.eval_surjective 0)]
  change RingHom.ker (Polynomial.evalRingHom (0 : R)) ≤ y.asIdeal ↔ _
  rw [Polynomial.ker_evalRingHom, map_zero, sub_zero, Ideal.span_singleton_le_iff_mem]

/-- The exact closed complement of the original polynomial chart is full infinity. -/
theorem range_infinity : Set.range (infinity R) = (Set.range (chart R))ᶜ := by
  have hdisj : Disjoint
      (Set.range (projectiveLineXChart R))
      (Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
        projectiveLineYChart R)) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, rfl⟩ ⟨z, hz⟩
    obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback
      (isPullback_projectiveLineCharts R) x
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) z) hz.symm
    have hn := (mem_range_projectiveLineOverlapYInclusion_iff R _).mp ⟨w, hw⟩
    exact hn ((mem_range_evalZero_iff R _).mp ⟨z, rfl⟩)
  have hcover : ∀ x : projectiveLine R,
      x ∈ Set.range (projectiveLineXChart R) ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
        projectiveLineYChart R) := by
    intro x
    obtain ⟨i, y, rfl⟩ := (projectiveLineGluingData R).ι_jointly_surjective x
    obtain ⟨i⟩ := i
    cases i
    · exact Or.inl ⟨y, rfl⟩
    · by_cases hy : (Polynomial.X : Polynomial R) ∈ y.asIdeal
      · obtain ⟨z, rfl⟩ := (mem_range_evalZero_iff R y).mpr hy
        exact Or.inr ⟨z, rfl⟩
      · obtain ⟨w, hw⟩ := (mem_range_projectiveLineOverlapYInclusion_iff R y).mpr hy
        left
        refine ⟨projectiveLinePuncturedChart R w, ?_⟩
        have he := congrArg (fun f => f w) (isPullback_projectiveLineCharts R).w
        change projectiveLineXChart R (projectiveLinePuncturedChart R w) =
          projectiveLineYChart R y
        simpa only [Scheme.Hom.comp_apply, hw] using he
  ext x
  obtain ⟨y, rfl⟩ := (projectiveLineIsoProjectiveSpaceOver R).hom.surjective x
  have he := (projectiveLineIsoProjectiveSpaceOver R).hom.isOpenEmbedding.injective
  constructor
  · rintro ⟨z, hz⟩ ⟨w, hw⟩
    exact Set.disjoint_left.mp hdisj ⟨w, he hw⟩ ⟨z, he hz⟩
  · intro hx
    rcases hcover y with ⟨w, hw⟩ | ⟨z, hz⟩
    · exact False.elim (hx ⟨w, congrArg (projectiveLineIsoProjectiveSpaceOver R).hom hw⟩)
    · exact ⟨z, congrArg (projectiveLineIsoProjectiveSpaceOver R).hom hz⟩

end AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine
