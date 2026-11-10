/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.SheafifiedChains
public import StacksFrontier.Homology.DerivedIndexing.Extend

/-!
# Cochain placement of ordinary algebraic singular chains

For a commutative ring `R`, the original ordinary singular chain degree `r`
is placed in integer cochain degree `q-r` using Mathlib's
`ComplexShape.embeddingUpIntLE`. Terms above `q` are zero. Canonical
sheafification is applied after this extension. The term, differential, and
homology comparisons use the native extension and exact-functor APIs.
The interchange between extension and sheafification is Stacks'
`DerivedIndexing.mapExtendIso`, with its actual component formula.

The transported differential retains the alternating face signs. This is
degree placement, not an identification with a signed shift: the latter needs
the separate component factor `(-1)^(q*r)`. These ordinary sheaf complexes are
not asserted to be motivic complexes or complexes of sheaves with transfers.

Adapted from `Motivic/Aglib/Algebra/Homology/SingularComplex/Indexing.lean`
and `Motivic/Aglib/Algebra/Homology/Sheafification/Singular.lean` at revision
`a6805c4a87cdfd7717dd7a94039246a167f15380`. No generic indexing wrapper or
second chain-complex model is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u v w

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A] [Abelian A]

/-- Place the actual ordinary singular chains in cochain degrees `q-r`. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/Algebra/Homology/Sheafification/Singular.lean:77-80"
  "adaptation" "Native extension of the relative algebraic singular presheaf complex"]
def singularCochainsFunctor (q : ℕ) : ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) ⥤
    CochainComplex ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) ℤ :=
  singularChainsFunctor R ⋙ (ComplexShape.embeddingUpIntLE (q : ℤ)).extendFunctor _

/-- The native term isomorphism identifies cochain degree `q-r` with chain degree `r`. -/
def singularCochainsXIso (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q r : ℕ) :
    ((singularCochainsFunctor R q).obj P).X ((q : ℤ) - r) ≅
      ((singularChainsFunctor R).obj P).X r :=
  ((singularChainsFunctor R).obj P).extendXIso (ComplexShape.embeddingUpIntLE (q : ℤ)) rfl

/-- Extension introduces zero terms above the chosen cochain bound. -/
theorem isZero_singularCochainsFunctor_obj_X
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero (((singularCochainsFunctor R q).obj P).X i) := by
  apply ((singularChainsFunctor R).obj P).isZero_extend_X
  exact (ComplexShape.notMem_range_embeddingUpIntLE_iff (q : ℤ) i).2 hi

variable (J : GrothendieckTopology (SmoothSite (Spec (.of R)))) [HasSheafify J A]

/-- Canonical sheafification after the original singular cochain placement. -/
def sheafifiedSingularCochainsFunctor (q : ℕ) :
    ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) ⥤ CochainComplex (Sheaf J A) ℤ :=
  singularCochainsFunctor R q ⋙
    (presheafToSheaf J A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- In degree `q-r`, the sheaf term is sheafification of the literal degree-`r` presheaf. -/
def sheafifiedSingularCochainsXIso
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q r : ℕ) :
    ((sheafifiedSingularCochainsFunctor R J q).obj P).X ((q : ℤ) - r) ≅
      (presheafToSheaf J A).obj (((singularChainsFunctor R).obj P).X r) :=
  (presheafToSheaf J A).mapIso (singularCochainsXIso R P q r)

/-- Sheafifying before or after native cochain extension gives canonically isomorphic complexes. -/
def sheafifiedSingularCochainsExtendIso
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q : ℕ) :
    (((sheafifiedSingularChainsFunctor R J).obj P).extend
      (ComplexShape.embeddingUpIntLE (q : ℤ))) ≅
        (sheafifiedSingularCochainsFunctor R J q).obj P :=
  Stacks.DerivedIndexing.mapExtendIso (presheafToSheaf J A)
    (ComplexShape.embeddingUpIntLE (q : ℤ)) ((singularChainsFunctor R).obj P)

/-- The extension/sheafification interchange preserves the original occupied term maps. -/
theorem sheafifiedSingularCochainsExtendIso_hom_f
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q r : ℕ) :
    (sheafifiedSingularCochainsExtendIso R J P q).hom.f ((q : ℤ) - r) =
      (((sheafifiedSingularChainsFunctor R J).obj P).extendXIso
        (ComplexShape.embeddingUpIntLE (q : ℤ)) (i := r) rfl).hom ≫
          (sheafifiedSingularCochainsXIso R J P q r).inv :=
  Stacks.DerivedIndexing.mapExtendIso_hom_f_eq (presheafToSheaf J A)
    (ComplexShape.embeddingUpIntLE (q : ℤ)) ((singularChainsFunctor R).obj P) rfl

/-- Canonical sheafification preserves the zero terms above the cochain bound. -/
theorem isZero_sheafifiedSingularCochainsFunctor_obj_X
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero (((sheafifiedSingularCochainsFunctor R J q).obj P).X i) :=
  (presheafToSheaf J A).map_isZero (isZero_singularCochainsFunctor_obj_X R P q i hi)

/-- The cochain differential is the original singular differential, without a shift sign. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/Algebra/Homology/Sheafification/Singular.lean:112-133"
  "adaptation" "Actual sheafified alternating differential under native q-r term isomorphisms"]
theorem sheafifiedSingularCochainsFunctor_obj_d
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q r s : ℕ) :
    ((sheafifiedSingularCochainsFunctor R J q).obj P).d ((q : ℤ) - r) ((q : ℤ) - s) =
      (sheafifiedSingularCochainsXIso R J P q r).hom ≫
        (presheafToSheaf J A).map (((singularChainsFunctor R).obj P).d r s) ≫
          (sheafifiedSingularCochainsXIso R J P q s).inv := by
  change (presheafToSheaf J A).map
    ((((singularChainsFunctor R).obj P).extend
      (ComplexShape.embeddingUpIntLE (q : ℤ))).d ((q : ℤ) - r) ((q : ℤ) - s)) =
    (presheafToSheaf J A).map
        (((singularChainsFunctor R).obj P).extendXIso
          (ComplexShape.embeddingUpIntLE (q : ℤ)) (i := r) (i' := (q : ℤ) - r) rfl).hom ≫
      (presheafToSheaf J A).map (((singularChainsFunctor R).obj P).d r s) ≫
        (presheafToSheaf J A).map
          (((singularChainsFunctor R).obj P).extendXIso
            (ComplexShape.embeddingUpIntLE (q : ℤ)) (i := s) (i' := (q : ℤ) - s) rfl).inv
  simpa only [Functor.map_comp] using
    congrArg (fun f => (presheafToSheaf J A).map f)
      (((singularChainsFunctor R).obj P).extend_d_eq
        (ComplexShape.embeddingUpIntLE (q : ℤ)) (i := r) (j := s)
        (i' := (q : ℤ) - r) (j' := (q : ℤ) - s) rfl rfl)

/-- In every occupied degree, cochain homology is sheafified ordinary singular homology. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/Algebra/Homology/Sheafification/Singular.lean:135-141"
  "adaptation" "Native extension and exact-sheafification homology comparisons"]
def sheafifiedSingularCochainsHomologyIso
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q r : ℕ) :
    ((sheafifiedSingularCochainsFunctor R J q).obj P).homology ((q : ℤ) - r) ≅
      (presheafToSheaf J A).obj (((singularChainsFunctor R).obj P).homology r) :=
  ((((singularCochainsFunctor R q).obj P).sc ((q : ℤ) - r)).mapHomologyIso
      (presheafToSheaf J A)) ≪≫
    (presheafToSheaf J A).mapIso
      (((singularChainsFunctor R).obj P).extendHomologyIso
        (ComplexShape.embeddingUpIntLE (q : ℤ)) rfl)

end AlgebraicSimplex

attribute [colib_tag "COL-0395"]
  AlgebraicSimplex.singularCochainsFunctor
  AlgebraicSimplex.sheafifiedSingularCochainsFunctor
  AlgebraicSimplex.sheafifiedSingularCochainsXIso
  AlgebraicSimplex.isZero_sheafifiedSingularCochainsFunctor_obj_X
  AlgebraicSimplex.sheafifiedSingularCochainsFunctor_obj_d
  AlgebraicSimplex.sheafifiedSingularCochainsHomologyIso
  AlgebraicSimplex.sheafifiedSingularCochainsExtendIso
  AlgebraicSimplex.sheafifiedSingularCochainsExtendIso_hom_f

attribute [colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/Homology/DerivedIndexing/Extend.lean:116-128"
  "specialization" "Native additive-functor extension interchange and occupied-degree component"]
  AlgebraicSimplex.sheafifiedSingularCochainsExtendIso
  AlgebraicSimplex.sheafifiedSingularCochainsExtendIso_hom_f
