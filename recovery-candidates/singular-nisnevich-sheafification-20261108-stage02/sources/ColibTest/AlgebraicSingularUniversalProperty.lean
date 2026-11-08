/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Simplex.NisnevichUniversalProperty

/-! # Actual chain-level Nisnevich adjunction and local homology consumers -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite AlgebraicSimplex HomologicalComplex
open AlgebraicGeometry.Scheme

universe u v w
variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A] [Abelian A]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))) A]
local notation "J" => SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))

variable (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)
variable (K : ChainComplex
  (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))) A) ℕ)

example : Nonempty
    (((nisnevichSingularChainsFunctor R).obj P ⟶ K) ≃
      ((singularChainsFunctor R).obj P ⟶
        ((sheafToPresheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)).obj K)) :=
  ⟨nisnevichSingularChainsHomEquiv R P K⟩

example (g : (nisnevichSingularChainsFunctor R).obj P ⟶ K) :
    nisnevichSingularChainsHomEquiv R P K g =
      singularChainsToNisnevichSheafification R P ≫
        ((sheafToPresheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)).map g :=
  nisnevichSingularChainsHomEquiv_apply R P K g

example (f : (singularChainsFunctor R).obj P ⟶
    ((sheafToPresheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)).obj K) (n : ℕ) :
    ((nisnevichSingularChainsHomEquiv R P K).symm f).f n =
      ((sheafificationAdjunction J A).homEquiv
        (((singularChainsFunctor R).obj P).X n) (K.X n)).symm (f.f n) :=
  nisnevichSingularChainsHomEquiv_symm_f R P K f n

example (f : (singularChainsFunctor R).obj P ⟶
    ((sheafToPresheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)).obj K) :
    ∃! g : (nisnevichSingularChainsFunctor R).obj P ⟶ K,
      singularChainsToNisnevichSheafification R P ≫
        ((sheafToPresheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)).map g = f :=
  existsUnique_nisnevichSingularChains_lift R P K f

variable {P} {Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q)

example (n : ℕ) : QuasiIsoAt ((nisnevichSingularChainsFunctor R).map α) n ↔
    IsIso ((presheafToSheaf J A).map
      (HomologicalComplex.homologyMap ((singularChainsFunctor R).map α) n)) :=
  nisnevichSingularChains_quasiIsoAt_iff R α n

example : QuasiIso ((nisnevichSingularChainsFunctor R).map α) ↔
    ∀ n, IsIso ((presheafToSheaf J A).map
      (HomologicalComplex.homologyMap ((singularChainsFunctor R).map α) n)) :=
  nisnevichSingularChains_quasiIso_iff R α

example [QuasiIso ((singularChainsFunctor R).map α)] :
    QuasiIso ((nisnevichSingularChainsFunctor R).map α) :=
  nisnevichSingularChains_quasiIso_of_quasiIso R α

example [IsIso α] : QuasiIso ((nisnevichSingularChainsFunctor R).map α) := inferInstance
