module

import Colib.AlgebraicGeometry.Simplex.NisnevichCoefficientComparison

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicSimplex

universe u v w
variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A] [Abelian A]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))) A]
variable (S : ShortComplex ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)) (hS : S.ShortExact)

example (n : ℕ) :
    nisnevichSingularCoefficientBoundary R S hS n ≫
        (nisnevichSingularHomologyIso R S.X₁ n).hom =
      (nisnevichSingularHomologyIso R S.X₃ (n + 1)).hom ≫
        (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))) A).map
          (singularCoefficientBoundary R S hS n) :=
  nisnevichSingularHomologyIso_hom_coefficientBoundary R S hS n

example (n : ℕ) :
    nisnevichSingularCoefficientBoundary R S hS n =
      (nisnevichSingularHomologyIso R S.X₃ (n + 1)).hom ≫
        (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))) A).map
          (singularCoefficientBoundary R S hS n) ≫
            (nisnevichSingularHomologyIso R S.X₁ n).inv :=
  nisnevichSingularCoefficientBoundary_eq R S hS n

example (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (m : ℤ) [Mono (m • 𝟙 P)] (n : ℕ) :
    nisnevichSingularCoefficientBoundary R (ShortComplex.cokernelSequence (m • 𝟙 P))
        (singularReduction_shortExact R P m) n ≫
          (nisnevichSingularHomologyIso R P n).hom =
      (nisnevichSingularHomologyIso R (cokernel (m • 𝟙 P)) (n + 1)).hom ≫
        (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))) A).map
          (singularBockstein R P m n) :=
  nisnevichSingularBockstein_comparison R P m n
