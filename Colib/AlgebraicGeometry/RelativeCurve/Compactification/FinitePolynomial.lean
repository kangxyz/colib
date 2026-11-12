/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.ProjectiveMap.NativeLine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteCompactification

/-! # Genuine normal finite compactification of a finite polynomial-coordinate map

The native relative normalization is Cartesian over the entire polynomial chart.
The boundary is its literal inverse image of the entire infinity section. Its
finiteness follows from the actual finite projective map, with no fibrewise
reduction and no unproved compactification assumption.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- A finite polynomial map supplies the compactification, full infinity and
all structural equations needed before choosing the retained smooth open. -/
theorem exists_native_finite_polynomial_compactification
    (k R : Type u) [Field k] [CommRing R] [IsNoetherianRing R]
    (r : Spec (.of R) ⟶ Spec (.of k)) [LocallyOfFiniteType r]
    {X : Scheme.{u}} [IsIntegral X] [IsNormal X]
    (f : X ⟶ Spec (.of (Polynomial R))) [IsFinite f] :
    ∃ (C D : Scheme.{u}) (j : X ⟶ C)
      (π : C ⟶ projectiveSpaceOverRing 1 (.of R)) (d : D ⟶ C),
      IsIntegral C ∧ IsNormal C ∧ IsLocallyNoetherian C ∧
      IsOpenImmersion j ∧ IsFinite π ∧ IsClosedImmersion d ∧
      IsFinite (d ≫ π ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))) ∧
      Set.range d = (Set.range j)ᶜ ∧
      IsPullback j f π (NativeProjectiveLine.chart R) ∧
      j ≫ π = f ≫ NativeProjectiveLine.chart R ∧
      j ≫ π ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) =
        f ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) := by
  let p := projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)
  have : QuasiCompact (NativeProjectiveLine.chart R) := inferInstance
  obtain ⟨C, π, j, hπ, hj, H, hdense, hnormal⟩ :=
    exists_isPullback_isFinite_relativeNormalization k (p ≫ r)
      (NativeProjectiveLine.chart R) f
  have : IsFinite π := hπ
  have : IsOpenImmersion j := hj
  have : IsDominant j := hdense
  have : IsNormal C := hnormal inferInstance
  have : IrreducibleSpace C := by
    rw [irreducibleSpace_def]
    convert ((IrreducibleSpace.isIrreducible_univ X).image _
      j.continuous.continuousOn).closure using 1
    simpa using j.denseRange.closure_range.symm
  have : IsIntegral C := isIntegral_of_irreducibleSpace_of_isReduced C
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (π ≫ p ≫ r)
  let D := pullback π (NativeProjectiveLine.infinity R)
  let d : D ⟶ C := pullback.fst π (NativeProjectiveLine.infinity R)
  have hdcomp : d ≫ π ≫ p = pullback.snd π (NativeProjectiveLine.infinity R) := by
    rw [← Category.assoc, pullback.condition, Category.assoc]
    simp only [p, NativeProjectiveLine.infinity_projection, Category.comp_id]
  have : IsFinite (d ≫ π ≫ p) := by rw [hdcomp]; infer_instance
  have hrj : Set.range j = π ⁻¹' Set.range (NativeProjectiveLine.chart R) := by
    ext c
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨f x, (congrArg (fun g => g x) H.w).symm⟩
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx, _⟩ := Scheme.exists_preimage_of_isPullback H c y hy.symm
      exact ⟨x, hx⟩
  refine ⟨C, D, j, π, d, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, ?_, H, H.w, ?_⟩
  · change Set.range (pullback.fst π (NativeProjectiveLine.infinity R)) = _
    rw [Scheme.Pullback.range_fst, NativeProjectiveLine.range_infinity, hrj]
    rfl
  · rw [← Category.assoc, H.w, Category.assoc, NativeProjectiveLine.chart_projection]

end AlgebraicGeometry.Scheme.RelativeCurve
