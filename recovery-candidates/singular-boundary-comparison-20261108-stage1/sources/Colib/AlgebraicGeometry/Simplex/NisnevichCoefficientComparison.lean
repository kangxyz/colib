/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.HomologySequenceMap
public import Colib.AlgebraicGeometry.Simplex.CoefficientSequence

/-!
# Nisnevich sheafification preserves the actual coefficient boundary

The native homology comparison for degreewise Nisnevich sheafification
commutes with the original connecting morphism of a short exact coefficient
sequence. Together with the established compatibility for the adjacent
homology maps, this identifies the actual long exact sequences, including
all connecting signs, rather than merely comparing their objects.

This fills the connecting-map comparison deliberately left open in
`CoefficientSequence`. The construction continues to use ordinary presheaves
on the actual smooth site. Neither Cor nor transfer sheafification is assumed.
For a Bockstein, the source remains the native cokernel of multiplication on
the original presheaf, with the original monomorphism hypothesis.

The proof uses the exact-functor compatibility of the native snake boundary.
Stacks Tag 0111 supplies the homology-sequence ingredient; MVW2006,
Definition 2.14, printed p. 16, supplies background for the ordinary singular
construction, not a claim that these generalized comparisons appear there
verbatim.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

universe u v w

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A] [Abelian A]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))) A]
variable (S : ShortComplex ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)) (hS : S.ShortExact)

/-- The actual Nisnevich homology comparison preserves the native connecting map. -/
@[colib_ref "MVW2006" "Lecture 2, Definition 2.14, p. 16"
  "background" "Underlying ordinary singular construction, not this categorical comparison"]
theorem nisnevichSingularHomologyIso_hom_coefficientBoundary (n : ℕ) :
    nisnevichSingularCoefficientBoundary R S hS n ≫
        (nisnevichSingularHomologyIso R S.X₁ n).hom =
      (nisnevichSingularHomologyIso R S.X₃ (n + 1)).hom ≫
        (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))) A).map
          (singularCoefficientBoundary R S hS n) :=
  HomologicalComplex.HomologySequence.mapHomologyIso_hom_δ
    (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))) A)
      (singularChainsFunctor_map_shortExact R S hS) (n + 1) n rfl

/-- The sheaf boundary is the original boundary transported through the native comparisons. -/
theorem nisnevichSingularCoefficientBoundary_eq (n : ℕ) :
    nisnevichSingularCoefficientBoundary R S hS n =
      (nisnevichSingularHomologyIso R S.X₃ (n + 1)).hom ≫
        (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))) A).map
          (singularCoefficientBoundary R S hS n) ≫
            (nisnevichSingularHomologyIso R S.X₁ n).inv := by
  apply (cancel_mono (nisnevichSingularHomologyIso R S.X₁ n).hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    nisnevichSingularHomologyIso_hom_coefficientBoundary R S hS n

/-- Compatibility also holds for the actual cokernel-multiplication Bockstein sequence. -/
theorem nisnevichSingularBockstein_comparison
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (m : ℤ) [Mono (m • 𝟙 P)] (n : ℕ) :
    nisnevichSingularCoefficientBoundary R (ShortComplex.cokernelSequence (m • 𝟙 P))
        (singularReduction_shortExact R P m) n ≫
          (nisnevichSingularHomologyIso R P n).hom =
      (nisnevichSingularHomologyIso R (cokernel (m • 𝟙 P)) (n + 1)).hom ≫
        (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))) A).map
          (singularBockstein R P m n) :=
  nisnevichSingularHomologyIso_hom_coefficientBoundary R
    (ShortComplex.cokernelSequence (m • 𝟙 P)) (singularReduction_shortExact R P m) n

end AlgebraicSimplex
