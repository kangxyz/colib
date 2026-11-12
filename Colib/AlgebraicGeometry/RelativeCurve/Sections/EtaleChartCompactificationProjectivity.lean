/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartCompactificationGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.Projectivity
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleRetainedGeometry

/-! # Projectivity of the unchanged chart compactification

The original finite projective-line cover supplies projectivity before base change.
The chart refinement then uses the native projective pullback theorem.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleChart

theorem compactifiedCurve_isProjective_of_finite_cover
    {R : Type u} [CommRing R] {A Z N : Scheme.{u}}
    (q : A ⟶ Z) (p : Z ⟶ Spec (.of R)) (s : Spec (.of R) ⟶ Z)
    (fN : N ⟶ Spec (.of R)) (π : N ⟶ projectiveLine R) [IsFinite π]
    (hπ : π ≫ (projectiveLine R ↘ Spec (.of R)) = fN) :
    IsProjectiveMorphism (pullback.fst (original q p s ≫ (q ≫ p)) fN) :=
  isProjectiveMorphism_pullback_fst fN (original q p s ≫ (q ≫ p))
    (isProjectiveMorphism_of_finite_projectiveLine R fN π hπ)

end AlgebraicGeometry.Scheme.EtaleChart
