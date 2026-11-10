/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.OrdinaryChains
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Sheafification of ordinary algebraic singular chains

Let `R` be a commutative ring, `J` a topology on its smooth site, and `A` an
abelian category with `HasSheafify J A`. Apply Mathlib's actual sheafification
degreewise to the existing complex with terms `U ↦ P(U ×[Spec R] Δⁿ)`.
The differential keeps the ordered barycentric faces and their integer signs.
The original sheafification unit is a chain map, natural in `P`, and exactness
of sheafification gives the native comparison on homology in every degree.

This specializes the ordinary construction of
`Motivic/Aglib/Algebra/Homology/Sheafification/Singular.lean` at revision
`a6805c4a87cdfd7717dd7a94039246a167f15380`, using the actual relative-product
simplices already in `OrdinaryChains`. The generic sheafification, chain-map,
and homology APIs remain Mathlib's. No transfer action or motivic complex is
asserted. In particular, the sheafification unit need not be a quasi-isomorphism
of the underlying presheaf complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicTopology
open AlgebraicGeometry.Scheme
open scoped Simplicial

universe u v w

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A] [Abelian A]
variable (J : GrothendieckTopology (SmoothSite (Spec (.of R)))) [HasSheafify J A]

/-- Degreewise canonical sheafification of the actual ordinary singular chains. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/Algebra/Homology/Sheafification/Singular.lean:44-47"
  "adaptation" "Ordinary relative algebraic singular chains with canonical sheafification"]
def sheafifiedSingularChainsFunctor : ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) ⥤
    ChainComplex (Sheaf J A) ℕ :=
  singularChainsFunctor R ⋙ (presheafToSheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)

@[simp]
theorem sheafifiedSingularChainsFunctor_obj_X
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (n : ℕ) :
    ((sheafifiedSingularChainsFunctor R J).obj P).X n =
      (presheafToSheaf J A).obj ((simplicialPresheaf R P).obj (op ⦋n⦌)) := rfl

/-- Every differential is the same alternating sum, followed by sheafification. -/
theorem sheafifiedSingularChainsFunctor_obj_d
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (n : ℕ) :
    ((sheafifiedSingularChainsFunctor R J).obj P).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (presheafToSheaf J A).map ((simplicialPresheaf R P).δ i) := by
  change (presheafToSheaf J A).map
    ((AlternatingFaceMapComplex.obj (simplicialPresheaf R P)).d (n + 1) n) = _
  rw [AlternatingFaceMapComplex.obj_d_eq]
  simp only [Functor.map_sum, Functor.map_zsmul]

@[simp]
theorem sheafifiedSingularChainsFunctor_map_f
    {P Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    ((sheafifiedSingularChainsFunctor R J).map α).f n =
      (presheafToSheaf J A).map (((singularChainsFunctor R).map α).f n) := rfl

/-- The original degreewise sheafification units form a natural chain map. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/Algebra/Homology/Sheafification/Singular.lean:62-69"
  "adaptation" "The canonical unit on the actual relative-product singular terms"]
def singularChainsSheafificationUnit : singularChainsFunctor R (A := A) ⟶
    sheafifiedSingularChainsFunctor R J ⋙
      (sheafToPresheaf J A).mapHomologicalComplex (ComplexShape.down ℕ) where
  app P :=
    { f n := toSheafify J (((singularChainsFunctor R).obj P).X n)
      comm' i j _ :=
        (toSheafify_naturality J (((singularChainsFunctor R).obj P).d i j)).symm }
  naturality P Q α := by
    ext n : 1
    exact toSheafify_naturality J (((singularChainsFunctor R).map α).f n)

@[simp]
theorem singularChainsSheafificationUnit_app_f
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (n : ℕ) :
    ((singularChainsSheafificationUnit R J).app P).f n =
      toSheafify J ((simplicialPresheaf R P).obj (op ⦋n⦌)) := rfl

/-- Homology of the sheafified singular chains is sheafified presheaf homology. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/Algebra/Homology/Sheafification/Singular.lean:71-75"
  "adaptation" "Native exact-functor homology comparison for ordinary algebraic singular chains"]
def sheafifiedSingularChainsHomologyIso
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (n : ℕ) :
    ((sheafifiedSingularChainsFunctor R J).obj P).homology n ≅
      (presheafToSheaf J A).obj (((singularChainsFunctor R).obj P).homology n) :=
  (((singularChainsFunctor R).obj P).sc n).mapHomologyIso (presheafToSheaf J A)

/-- The native homology comparison keeps the actual maps of coefficient presheaves. -/
@[reassoc]
theorem sheafifiedSingularChainsHomologyIso_hom_naturality
    {P Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    HomologicalComplex.homologyMap ((sheafifiedSingularChainsFunctor R J).map α) n ≫
        (sheafifiedSingularChainsHomologyIso R J Q n).hom =
      (sheafifiedSingularChainsHomologyIso R J P n).hom ≫
        (presheafToSheaf J A).map
          (HomologicalComplex.homologyMap ((singularChainsFunctor R).map α) n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.down ℕ) n).map
      ((singularChainsFunctor R).map α)) (presheafToSheaf J A)

end AlgebraicSimplex

attribute [colib_tag "COL-0395"]
  AlgebraicSimplex.sheafifiedSingularChainsFunctor
  AlgebraicSimplex.sheafifiedSingularChainsFunctor_obj_d
  AlgebraicSimplex.singularChainsSheafificationUnit
  AlgebraicSimplex.sheafifiedSingularChainsHomologyIso
  AlgebraicSimplex.sheafifiedSingularChainsHomologyIso_hom_naturality
