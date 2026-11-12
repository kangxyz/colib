/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.ProjectiveMap.NativeLine

/-!
# The two actual polynomial charts of the native relative projective line

Both chart maps are the native gluing maps followed by the same comparison
to projective space over the coefficient ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine

variable (R : Type u) [CommRing R]

/-- The two actual polynomial chart maps in their gluing order. -/
def polynomialCharts : Fin 2 → (Spec (.of (Polynomial R)) ⟶ projectiveSpaceOverRing 1 (.of R)) :=
  Fin.cases (chart R) (fun _ ↦
    projectiveLineYChart R ≫ (projectiveLineIsoProjectiveSpaceOver R).hom)

@[simp]
theorem polynomialCharts_zero : polynomialCharts R 0 = chart R := rfl

@[simp]
theorem polynomialCharts_one :
    polynomialCharts R 1 = projectiveLineYChart R ≫ (projectiveLineIsoProjectiveSpaceOver R).hom :=
  rfl

instance polynomialCharts_open (i : Fin 2) : IsOpenImmersion (polynomialCharts R i) := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change IsOpenImmersion (chart R)
    infer_instance
  · change IsOpenImmersion
      (projectiveLineYChart R ≫ (projectiveLineIsoProjectiveSpaceOver R).hom)
    infer_instance

/-- The two literal polynomial charts cover the whole projective line. -/
theorem exists_mem_range_polynomialCharts (x : projectiveSpaceOverRing 1 (.of R)) :
    ∃ i, x ∈ Set.range (polynomialCharts R i) := by
  by_cases hx : x ∈ Set.range (chart R)
  · exact ⟨0, by simpa only [polynomialCharts_zero] using hx⟩
  · have hi : x ∈ Set.range (infinity R) := by rwa [range_infinity]
    obtain ⟨y, hy⟩ := hi
    refine ⟨1, Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) y, ?_⟩
    simpa only [polynomialCharts_one, infinity, Scheme.Hom.comp_apply] using hy

/-- Both polynomial charts are over the same original coefficient map. -/
@[reassoc (attr := simp)]
theorem polynomialCharts_projection (i : Fin 2) :
    polynomialCharts R i ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact chart_projection R
  · change (projectiveLineYChart R ≫ (projectiveLineIsoProjectiveSpaceOver R).hom) ≫
      (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) = _
    rw [Category.assoc, projectiveLineIsoProjectiveSpaceOver_hom_fst,
      projectiveLineYChart_comp_structureMorphism]

end AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine
