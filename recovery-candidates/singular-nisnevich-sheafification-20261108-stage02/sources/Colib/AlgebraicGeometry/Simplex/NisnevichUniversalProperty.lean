/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.NisnevichSheafification
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Universal property and local homology criterion for ordinary Nisnevich chains

The native Stacks adjunction on homological complexes gives the universal
property of degreewise Nisnevich sheafification of the actual ordinary singular
complex. The transpose has the original coefficient sheafification transpose
in each degree. We do not construct a second adjunction or chain carrier.

A coefficient map induces a quasi-isomorphism of these sheaf complexes exactly
when its original singular-homology maps become isomorphisms after native
sheafification. Original quasi-isomorphisms therefore remain quasi-isomorphisms.
The reverse implication to an original presheaf quasi-isomorphism is not
asserted: sheafification does not generally reflect isomorphisms.

The adjunction ingredient is
`StacksFrontier/CategoryTheory/Localization/DerivingAdjoints.lean:655,695`
at Stacks revision `5ed82d14634e8d9576bb844c7bd4e3da66d450e7`.
The homology criterion uses the native Mathlib `QuasiIso` predicate and the
already established natural homology comparison. No transfer category or
motivic-derived localization is assumed or constructed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite HomologicalComplex
open AlgebraicGeometry.Scheme

universe u v w

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A] [Abelian A]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))) A]

local notation "J" => SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))

/-- The actual chain-level adjunction, restricted to the existing singular complex. -/
def nisnevichSingularChainsHomEquiv
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (K : ChainComplex (Sheaf J A) ℕ) :
    (((nisnevichSingularChainsFunctor R).obj P) ⟶ K) ≃
      (((singularChainsFunctor R).obj P) ⟶
        ((sheafToPresheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)).obj K) :=
  ((sheafificationAdjunction J A).mapHomologicalComplexAdjunction
    (ComplexShape.down ℕ)).homEquiv ((singularChainsFunctor R).obj P) K

/-- The universal map is precisely the existing sheafification unit, not a new one. -/
theorem nisnevichSingularChainsHomEquiv_apply
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (K : ChainComplex (Sheaf J A) ℕ)
    (g : ((nisnevichSingularChainsFunctor R).obj P) ⟶ K) :
    nisnevichSingularChainsHomEquiv R P K g =
      singularChainsToNisnevichSheafification R P ≫
        ((sheafToPresheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)).map g := rfl

/-- The inverse transpose remains the actual coefficient transpose in every degree. -/
theorem nisnevichSingularChainsHomEquiv_symm_f
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (K : ChainComplex (Sheaf J A) ℕ)
    (f : ((singularChainsFunctor R).obj P) ⟶
      ((sheafToPresheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)).obj K) (n : ℕ) :
    ((nisnevichSingularChainsHomEquiv R P K).symm f).f n =
      ((sheafificationAdjunction J A).homEquiv
        (((singularChainsFunctor R).obj P).X n) (K.X n)).symm (f.f n) := rfl

/-- Every map into a genuine sheaf complex factors uniquely through the original unit. -/
theorem existsUnique_nisnevichSingularChains_lift
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (K : ChainComplex (Sheaf J A) ℕ)
    (f : ((singularChainsFunctor R).obj P) ⟶
      ((sheafToPresheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)).obj K) :
    ∃! g : ((nisnevichSingularChainsFunctor R).obj P) ⟶ K,
      singularChainsToNisnevichSheafification R P ≫
        ((sheafToPresheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)).map g = f := by
  let e := nisnevichSingularChainsHomEquiv R P K
  refine ⟨e.symm f, e.apply_symm_apply f, ?_⟩
  intro g hg
  exact e.injective (hg.trans (e.apply_symm_apply f).symm)

/-- Degreewise quasi-isomorphism is detected on the sheafified original homology map. -/
theorem nisnevichSingularChains_quasiIsoAt_iff
    {P Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    QuasiIsoAt ((nisnevichSingularChainsFunctor R).map α) n ↔
      IsIso ((presheafToSheaf J A).map
        (HomologicalComplex.homologyMap ((singularChainsFunctor R).map α) n)) := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  rw [← isIso_comp_right_iff _ (nisnevichSingularHomologyIso R Q n).hom,
    nisnevichSingularHomologyIso_hom_naturality,
    isIso_comp_left_iff]

/-- The actual sheafified singular complex detects precisely local homology isomorphisms. -/
theorem nisnevichSingularChains_quasiIso_iff
    {P Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q) :
    QuasiIso ((nisnevichSingularChainsFunctor R).map α) ↔
      ∀ n, IsIso ((presheafToSheaf J A).map
        (HomologicalComplex.homologyMap ((singularChainsFunctor R).map α) n)) := by
  rw [quasiIso_iff]
  exact forall_congr' (fun n => nisnevichSingularChains_quasiIsoAt_iff R α n)

/-- Sheafification preserves original singular-chain quasi-isomorphisms, without reflection. -/
theorem nisnevichSingularChains_quasiIso_of_quasiIso
    {P Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q)
    [QuasiIso ((singularChainsFunctor R).map α)] :
    QuasiIso ((nisnevichSingularChainsFunctor R).map α) :=
  inferInstanceAs (QuasiIso
    (((presheafToSheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)).map
      ((singularChainsFunctor R).map α)))

end AlgebraicSimplex
