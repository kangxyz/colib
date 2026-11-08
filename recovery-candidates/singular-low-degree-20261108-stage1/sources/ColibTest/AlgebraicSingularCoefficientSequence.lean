module

import Colib.AlgebraicGeometry.Simplex.CoefficientSequence

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open AlgebraicSimplex

universe u v w

variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A] [Abelian A]
variable (S T : ShortComplex ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A))
variable (hS : S.ShortExact) (hT : T.ShortExact)

example (n : ℕ) :
    ((singularChainsFunctor R).obj S.X₃).homology (n + 1) ⟶
      ((singularChainsFunctor R).obj S.X₁).homology n :=
  singularCoefficientBoundary R S hS n

example : (ComposableArrows.mk₅
    (HomologicalComplex.homologyMap ((singularChainsFunctor R).map S.f) 1)
    (HomologicalComplex.homologyMap ((singularChainsFunctor R).map S.g) 1)
    (singularCoefficientBoundary R S hS 0)
    (HomologicalComplex.homologyMap ((singularChainsFunctor R).map S.f) 0)
    (HomologicalComplex.homologyMap ((singularChainsFunctor R).map S.g) 0)).Exact :=
  singularCoefficientSequence_exact R S hS 0

example : Epi (HomologicalComplex.homologyMap ((singularChainsFunctor R).map S.g) 0) :=
  epi_singularHomologyZeroMap R S hS

example (φ : S ⟶ T) (n : ℕ) :
    singularCoefficientBoundary R S hS n ≫
        HomologicalComplex.homologyMap ((singularChainsFunctor R).map φ.τ₁) n =
      HomologicalComplex.homologyMap ((singularChainsFunctor R).map φ.τ₃) (n + 1) ≫
        singularCoefficientBoundary R T hT n :=
  singularCoefficientBoundary_naturality R hS hT φ n

example (n : ℕ)
    (hi : IsZero (((singularChainsFunctor R).obj S.X₂).homology (n + 1)))
    (hj : IsZero (((singularChainsFunctor R).obj S.X₂).homology n)) :
    (singularCoefficientBoundaryIso R S hS n hi hj).hom =
      singularCoefficientBoundary R S hS n :=
  singularCoefficientBoundaryIso_hom R S hS n hi hj

example (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (m : ℤ) [Mono (m • 𝟙 P)] :
    (ShortComplex.cokernelSequence (m • 𝟙 P)).ShortExact :=
  singularReduction_shortExact R P m

example (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (m : ℤ) [Mono (m • 𝟙 P)] (n : ℕ) :
    singularBockstein R P m n ≫
      HomologicalComplex.homologyMap ((singularChainsFunctor R).map (m • 𝟙 P)) n = 0 :=
  singularBockstein_comp_multiplication R P m n

variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))) A]

example : Epi (HomologicalComplex.homologyMap
    ((nisnevichSingularChainsFunctor R).map S.g) 0) :=
  epi_nisnevichSingularHomologyZeroMap R S hS

example : (ComposableArrows.mk₅
    (HomologicalComplex.homologyMap ((nisnevichSingularChainsFunctor R).map S.f) 1)
    (HomologicalComplex.homologyMap ((nisnevichSingularChainsFunctor R).map S.g) 1)
    (nisnevichSingularCoefficientBoundary R S hS 0)
    (HomologicalComplex.homologyMap ((nisnevichSingularChainsFunctor R).map S.f) 0)
    (HomologicalComplex.homologyMap ((nisnevichSingularChainsFunctor R).map S.g) 0)).Exact :=
  nisnevichSingularCoefficientSequence_exact R S hS 0

example (φ : S ⟶ T) (n : ℕ) :
    nisnevichSingularCoefficientBoundary R S hS n ≫
        HomologicalComplex.homologyMap ((nisnevichSingularChainsFunctor R).map φ.τ₁) n =
      HomologicalComplex.homologyMap ((nisnevichSingularChainsFunctor R).map φ.τ₃) (n + 1) ≫
        nisnevichSingularCoefficientBoundary R T hT n :=
  nisnevichSingularCoefficientBoundary_naturality R hS hT φ n
