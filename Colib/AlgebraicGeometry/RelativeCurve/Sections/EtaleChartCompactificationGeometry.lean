/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartCompactifiedSections
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Normal proper compactification over the original chart refinement

Normality is obtained from the second, smooth projection to the original normal
compactification. No integrality of the base-changed compactification is inferred.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleChart
variable {A Y Z N : Scheme.{u}}
  (q : A ⟶ Z) (p : Z ⟶ Y) (s : Y ⟶ Z) (fN : N ⟶ Y)

instance compactifiedCurve_isProper [IsProper fN] :
    IsProper (pullback.fst (original q p s ≫ (q ≫ p)) fN) := inferInstance

/-- The original projection is etale and the original tail coordinate is smooth. -/
theorem refinement_to_tail_smooth [Etale q] [Smooth p] :
    Smooth (original q p s ≫ (q ≫ p)) := inferInstance

/-- The new curve is normal because its projection to the old normal curve is smooth. -/
theorem compactifiedCurve_isNormal [Etale q] [Smooth p] [IsNormal N] :
    IsNormal (compactifiedCurve q p s fN) := by
  have : Smooth (original q p s ≫ (q ≫ p)) :=
    refinement_to_tail_smooth q p s
  exact isNormal_of_smooth (pullback.snd (original q p s ≫ (q ≫ p)) fN)

/-- The map to the independent original normal model is flat, as needed by the chart lemma. -/
instance compactifiedCurve_toOriginal_flat [Etale q] [Smooth p] :
    Flat (pullback.snd (original q p s ≫ (q ≫ p)) fN) := by
  have : Smooth (original q p s ≫ (q ≫ p)) :=
    refinement_to_tail_smooth q p s
  infer_instance
end AlgebraicGeometry.Scheme.EtaleChart
