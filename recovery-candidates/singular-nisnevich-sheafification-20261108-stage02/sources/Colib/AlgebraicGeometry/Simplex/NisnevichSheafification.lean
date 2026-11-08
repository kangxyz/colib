/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.Exactness
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Degreewise Nisnevich sheafification of ordinary singular chains

Apply the native `presheafToSheaf` degreewise to the existing ordinary singular
complex on the actual smooth Nisnevich site. Both chain carriers, the topology,
and the sheafification are their existing native constructions. The original
sheafification unit is a chain map, natural in the coefficient presheaf.

Sheafification is a left exact left adjoint, hence is exact for abelian
coefficients. We identify the homology of the sheafified complex with the
sheafification of the original presheaf homology, retaining the native homology
comparison and its coefficient naturality. The resulting functor preserves
short exact sequences of ordinary presheaves.

The general statements assume the native `HasSheafify` property. For a base
ring in universe `u`, the actual coefficient category `AddCommGrpCat.{u+1}`
satisfies it by Mathlib's concrete sheafification construction; no small-site
replacement or additional sheafification axiom is required.

This is not a transfer construction. In particular, we do not identify
sheafification before and after simplex-product precomposition, and do not
claim that sheafification preserves homotopy invariance. Native references are
`Sites/Sheafification.lean` (left exact adjunction), `Sites/LeftExact.lean`
(concrete existence), and `ShortComplex/PreservesHomology.lean` (the homology
comparison). The ordinary complex is MVW2006, Definition 2.14, printed p. 16.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

universe u v w a b

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]

local notation "J" => SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))

/-- Concrete abelian-group sheafification exists in the site's natural large universe. -/
theorem hasNisnevichSheafification_addCommGrp : HasSheafify J AddCommGrpCat.{u + 1} :=
  inferInstance

variable {A : Type v} [Category.{w} A] [Abelian A]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))) A]

/-- The original ordinary chains, sheafified degreewise on the actual Nisnevich site. -/
def nisnevichSingularChainsFunctor :
    ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) ⥤ ChainComplex (Sheaf J A) ℕ :=
  singularChainsFunctor R ⋙ (presheafToSheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)

/-- In each degree this is the native sheafification of the original simplex presheaf. -/
theorem nisnevichSingularChainsFunctor_obj_X
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (n : ℕ) :
    ((nisnevichSingularChainsFunctor R).obj P).X n =
      (presheafToSheaf J A).obj (((singularChainsFunctor R).obj P).X n) := rfl

/-- No new differential is chosen: it is the image of the original alternating differential. -/
theorem nisnevichSingularChainsFunctor_obj_d
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (i j : ℕ) :
    ((nisnevichSingularChainsFunctor R).obj P).d i j =
      (presheafToSheaf J A).map (((singularChainsFunctor R).obj P).d i j) := rfl

/-- Coefficient transformations are the original chain maps followed by sheafification. -/
theorem nisnevichSingularChainsFunctor_map_f
    {P Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    ((nisnevichSingularChainsFunctor R).map α).f n =
      (presheafToSheaf J A).map (((singularChainsFunctor R).map α).f n) := rfl

instance : (nisnevichSingularChainsFunctor R (A := A)).Additive :=
  inferInstanceAs (singularChainsFunctor R ⋙
    (presheafToSheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)).Additive

instance : PreservesFiniteLimits (nisnevichSingularChainsFunctor R (A := A)) :=
  inferInstanceAs (PreservesFiniteLimits (singularChainsFunctor R ⋙
    (presheafToSheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)))

instance : PreservesFiniteColimits (nisnevichSingularChainsFunctor R (A := A)) :=
  inferInstanceAs (PreservesFiniteColimits (singularChainsFunctor R ⋙
    (presheafToSheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)))

instance (K : Type a) [Category.{b} K] [HasColimitsOfShape K A] :
    PreservesColimitsOfShape K (nisnevichSingularChainsFunctor R (A := A)) :=
  inferInstanceAs (PreservesColimitsOfShape K (singularChainsFunctor R ⋙
    (presheafToSheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)))

/-- The sheafification unit on the original complex, with its original degree components. -/
def singularChainsToNisnevichSheafification
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) :
    (singularChainsFunctor R).obj P ⟶
      ((sheafToPresheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((nisnevichSingularChainsFunctor R).obj P) :=
  (NatTrans.mapHomologicalComplex (sheafificationAdjunction J A).unit
    (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P)

theorem singularChainsToNisnevichSheafification_f
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (n : ℕ) :
    (singularChainsToNisnevichSheafification R P).f n =
      toSheafify J (((singularChainsFunctor R).obj P).X n) := rfl

/-- The chain-level sheafification unit is natural for the original coefficient maps. -/
@[reassoc]
theorem singularChainsToNisnevichSheafification_naturality
    {P Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q) :
    (singularChainsFunctor R).map α ≫ singularChainsToNisnevichSheafification R Q =
      singularChainsToNisnevichSheafification R P ≫
        ((sheafToPresheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)).map
          ((nisnevichSingularChainsFunctor R).map α) :=
  (NatTrans.mapHomologicalComplex (sheafificationAdjunction J A).unit
    (ComplexShape.down ℕ)).naturality ((singularChainsFunctor R).map α)

/-- Homology commutes with this degreewise sheafification via the native comparison. -/
def nisnevichSingularHomologyIso
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (n : ℕ) :
    ((nisnevichSingularChainsFunctor R).obj P).homology n ≅
      (presheafToSheaf J A).obj (((singularChainsFunctor R).obj P).homology n) :=
  (((singularChainsFunctor R).obj P).sc n).mapHomologyIso (presheafToSheaf J A)

/-- The homology comparison preserves the actual coefficient-induced homology maps. -/
@[reassoc]
theorem nisnevichSingularHomologyIso_hom_naturality
    {P Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    HomologicalComplex.homologyMap ((nisnevichSingularChainsFunctor R).map α) n ≫
      (nisnevichSingularHomologyIso R Q n).hom =
        (nisnevichSingularHomologyIso R P n).hom ≫
          (presheafToSheaf J A).map
            (HomologicalComplex.homologyMap ((singularChainsFunctor R).map α) n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.down ℕ) n).map
      ((singularChainsFunctor R).map α)) (presheafToSheaf J A)

/-- An exact sequence remains exact after ordinary singular chains and sheafification. -/
theorem nisnevichSingularChainsFunctor_map_exact
    (S : ShortComplex ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)) (h : S.Exact) :
    (S.map (nisnevichSingularChainsFunctor R)).Exact := h.map _

/-- Short exactness holds in the actual category of chain complexes of Nisnevich sheaves. -/
theorem nisnevichSingularChainsFunctor_map_shortExact
    (S : ShortComplex ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)) (h : S.ShortExact) :
    (S.map (nisnevichSingularChainsFunctor R)).ShortExact := h.map_of_exact _

end AlgebraicSimplex
