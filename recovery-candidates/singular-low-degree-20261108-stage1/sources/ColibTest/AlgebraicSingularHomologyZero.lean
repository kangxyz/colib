module

import Colib.AlgebraicGeometry.Simplex.HomologyZero

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite AlgebraicTopology
open AlgebraicGeometry.Scheme
open scoped Simplicial

universe u v w

variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A] [Abelian A]
variable (P Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)

example : Epi (AlgebraicSimplex.singularHomologyZeroπ R P) := inferInstance

example : ((AlgebraicSimplex.singularChainsFunctor R).obj P).d 1 0 ≫
    AlgebraicSimplex.singularHomologyZeroπ R P = 0 :=
  AlgebraicSimplex.singularChains_d_comp_homologyZeroπ R P

example : (AlgebraicSimplex.simplicialPresheaf R P).δ (0 : Fin 2) ≫
    AlgebraicSimplex.singularHomologyZeroπ R P =
      (AlgebraicSimplex.simplicialPresheaf R P).δ (1 : Fin 2) ≫
        AlgebraicSimplex.singularHomologyZeroπ R P :=
  AlgebraicSimplex.singularFaces_comp_homologyZeroπ R P

example (f : ((AlgebraicSimplex.singularChainsFunctor R).obj P).X 0 ⟶ Q)
    (hf : (AlgebraicSimplex.simplicialPresheaf R P).δ (0 : Fin 2) ≫ f =
      (AlgebraicSimplex.simplicialPresheaf R P).δ (1 : Fin 2) ≫ f) :
    ∃! g : ((AlgebraicSimplex.singularChainsFunctor R).obj P).homology 0 ⟶ Q,
      AlgebraicSimplex.singularHomologyZeroπ R P ≫ g = f :=
  AlgebraicSimplex.existsUnique_singularHomologyZeroDesc R P f hf

example (α : P ⟶ Q) :
    AlgebraicSimplex.singularHomologyZeroπ R P ≫
      HomologicalComplex.homologyMap ((AlgebraicSimplex.singularChainsFunctor R).map α) 0 =
        ((AlgebraicSimplex.singularChainsFunctor R).map α).f 0 ≫
          AlgebraicSimplex.singularHomologyZeroπ R Q :=
  AlgebraicSimplex.singularHomologyZeroπ_naturality R α

example (f g : ((AlgebraicSimplex.singularChainsFunctor R).obj P).homology 0 ⟶ Q)
    (h : AlgebraicSimplex.singularHomologyZeroπ R P ≫ f =
      AlgebraicSimplex.singularHomologyZeroπ R P ≫ g) : f = g :=
  AlgebraicSimplex.singularHomologyZero_hom_ext R P h
