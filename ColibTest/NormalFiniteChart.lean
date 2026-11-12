/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Normalization.Compactification.FiniteBoundary
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

/-- The construction retains the given smooth curve, without requiring the compactification
itself to be smooth. -/
example {X Y Z S E : Scheme.{u}} [IsIntegral X] [IsNormal X] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) [IsFinite f] (j : Y ⟶ Z) [IsOpenImmersion j] [QuasiCompact j]
    (hZ : IsNagataScheme Z) (q : Z ⟶ S) [IsProper q]
    (d : E ⟶ Z) [IsClosedImmersion d] [IsFinite (d ≫ q)]
    (hd : Set.range d = (Set.range j)ᶜ) [SmoothOfRelativeDimension 1 (f ≫ j ≫ q)] :
    ∃ (N D : Scheme.{u}) (i : X ⟶ N) (π : N ⟶ Z) (b : D ⟶ N) (e : D ⟶ E),
      IsIntegral N ∧ IsLocallyNoetherian N ∧ IsNormal N ∧
      IsOpenImmersion i ∧ IsFinite π ∧ IsProper (π ≫ q) ∧ IsClosedImmersion b ∧
      IsFinite (b ≫ π ≫ q) ∧ IsPullback b e π d ∧ Set.range b = (Set.range i)ᶜ ∧
      SmoothOfRelativeDimension 1 (i ≫ π ≫ q) := by
  obtain ⟨N, D, i, π, b, e, hN, hn, hnormal, hi, hπ, hproper, hb, hfinite, hpb, hfull, _, hfac⟩ :=
    Scheme.exists_normal_proper_compactification_of_finite_chart f j hZ q d hd
  exact ⟨N, D, i, π, b, e, hN, hn, hnormal, hi, hπ, hproper, hb, hfinite, hpb, hfull,
    hfac.symm ▸ inferInstance⟩

/-- Full-chart retention applies to the original normalization, not a second chosen envelope. -/
example {X Z : Scheme.{u}} (g : X ⟶ Z) [QuasiCompact g] [QuasiSeparated g]
    (U : Z.Opens) [IsIntegralHom (pullback.snd g U.ι)] (hU : g ⁻¹ᵁ U = ⊤) :
    Set.range g.toNormalization = g.fromNormalization ⁻¹' (U : Set Z) :=
  g.range_toNormalization_eq_preimage_integral_chart U hU

#print axioms AlgebraicGeometry.Scheme.Hom.mem_range_toNormalization_of_integral_chart
#print axioms AlgebraicGeometry.Scheme.Hom.range_toNormalization_eq_preimage_integral_chart
#print axioms AlgebraicGeometry.Scheme.Hom.isNormal_normalization_of_integral_source
#print axioms AlgebraicGeometry.Scheme.exists_normal_finite_cover_of_nagata_finite_chart
#print axioms AlgebraicGeometry.Scheme.exists_normal_proper_compactification_of_finite_chart
