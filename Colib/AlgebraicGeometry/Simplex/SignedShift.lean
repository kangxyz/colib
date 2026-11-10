/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.Embedding.SignedShift
public import Colib.AlgebraicGeometry.Simplex.OrdinaryCochains

/-!
# Signed shifts of ordinary algebraic singular cochains

The existing placement in degree `q-r` is naturally isomorphic to the actual
weight-zero cochain complex shifted by `-q`. Its component on chain degree `r`
is `(-1)^(q*r)`, and this sign compensates for the signed shift differential.
Canonical degreewise sheafification preserves the comparison and its signs.

This specializes `Motivic/Aglib/Algebra/Homology/SingularComplex/SignedShift.lean`
at revision `a6805c4a87cdfd7717dd7a94039246a167f15380` to the already selected
relative algebraic simplex and its actual ordinary presheaf chains. It does not
introduce a transfer action or identify a reduced-torus motivic input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u v w

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A] [Abelian A]

/-- The ordinary cochain placement is naturally the actual signed shift of weight zero. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/Algebra/Homology/SingularComplex/SignedShift.lean:43-46"
  "adaptation" "The native relative algebraic singular placement and signed shift"]
def singularCochainsShiftNatIso (q : ℕ) :
    singularCochainsFunctor (A := A) R q ≅
      singularCochainsFunctor R 0 ⋙
        CategoryTheory.shiftFunctor
          (CochainComplex ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) ℤ) (-(q : ℤ)) :=
  Functor.isoWhiskerLeft (singularChainsFunctor (A := A) R)
    (HomologicalComplex.ExtensionSignedShift.naturalIso q)

/-- The signed comparison for an actual ordinary presheaf. -/
def singularCochainsShiftIso (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q : ℕ) :
    (singularCochainsFunctor R q).obj P ≅
      ((singularCochainsFunctor R 0).obj P)⟦-(q : ℤ)⟧ :=
  (singularCochainsShiftNatIso R q).app P

/-- The occupied term of the actual signed shift is the original chain term. -/
def singularCochainsShiftedXIso
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q r : ℕ) :
    (((singularCochainsFunctor R 0).obj P)⟦-(q : ℤ)⟧).X ((q : ℤ) - r) ≅
      ((singularChainsFunctor R).obj P).X r :=
  HomologicalComplex.ExtensionSignedShift.shiftedXIso
    ((singularChainsFunctor R).obj P) q r rfl

/-- The component multiplier is exactly `(-1)^(q*r)`, not a sign-free identification. -/
theorem singularCochainsShiftIso_hom_f
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q r : ℕ) :
    (singularCochainsShiftIso R P q).hom.f ((q : ℤ) - r) =
      (-1 : ℤ) ^ (q * r) •
        ((singularCochainsXIso R P q r).hom ≫
          (singularCochainsShiftedXIso R P q r).inv) := by
  change (HomologicalComplex.ExtensionSignedShift.iso
    ((singularChainsFunctor R).obj P) q).hom.f ((q : ℤ) - r) = _
  rw [HomologicalComplex.ExtensionSignedShift.iso_hom_f]
  change ((q : ℤ) * r).negOnePow •
      ((singularCochainsXIso R P q r).hom ≫
        (singularCochainsShiftedXIso R P q r).inv) = _
  rw [Units.smul_def, ← Nat.cast_mul, Int.coe_negOnePow_natCast]

/-- The actual signed-shift differential retains its native integer shift sign. -/
theorem singularCochainsShifted_d
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q r s : ℕ) :
    (((singularCochainsFunctor R 0).obj P)⟦-(q : ℤ)⟧).d
        ((q : ℤ) - r) ((q : ℤ) - s) =
      (-(q : ℤ)).negOnePow •
        ((singularCochainsShiftedXIso R P q r).hom ≫
          ((singularChainsFunctor R).obj P).d r s ≫
            (singularCochainsShiftedXIso R P q s).inv) :=
  HomologicalComplex.ExtensionSignedShift.shifted_d
    ((singularChainsFunctor R).obj P) q r s

/-- All differentials, including the zero terms, commute with the comparison. -/
theorem singularCochainsShiftIso_comm
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q : ℕ) (i j : ℤ) :
    (singularCochainsShiftIso R P q).hom.f i ≫
        (((singularCochainsFunctor R 0).obj P)⟦-(q : ℤ)⟧).d i j =
      ((singularCochainsFunctor R q).obj P).d i j ≫
        (singularCochainsShiftIso R P q).hom.f j :=
  (singularCochainsShiftIso R P q).hom.comm i j

/-- The comparison is natural in the actual presheaf morphism. -/
theorem singularCochainsShiftIso_naturality
    {P Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q) (q : ℕ) :
    (singularCochainsFunctor R q).map α ≫ (singularCochainsShiftIso R Q q).hom =
      (singularCochainsShiftIso R P q).hom ≫
        (CategoryTheory.shiftFunctor
          (CochainComplex ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) ℤ) (-(q : ℤ))).map
          ((singularCochainsFunctor R 0).map α) :=
  (singularCochainsShiftNatIso R q).hom.naturality α

/-- All component signs are positive at weight two. -/
theorem singularCochainsShiftIso_two_hom_f
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (r : ℕ) :
    (singularCochainsShiftIso R P 2).hom.f ((2 : ℤ) - r) =
      (singularCochainsXIso R P 2 r).hom ≫
        (singularCochainsShiftedXIso R P 2 r).inv := by
  simpa [pow_mul] using singularCochainsShiftIso_hom_f R P 2 r

variable (J : GrothendieckTopology (SmoothSite (Spec (.of R)))) [HasSheafify J A]

/-- Degreewise sheafification preserves the actual signed comparison naturally. -/
def sheafifiedSingularCochainsShiftNatIso (q : ℕ) :
    sheafifiedSingularCochainsFunctor (A := A) R J q ≅
      sheafifiedSingularCochainsFunctor R J 0 ⋙
        CategoryTheory.shiftFunctor (CochainComplex (Sheaf J A) ℤ) (-(q : ℤ)) :=
  Functor.isoWhiskerRight (singularCochainsShiftNatIso R q)
      ((presheafToSheaf J A).mapHomologicalComplex (ComplexShape.up ℤ)) ≪≫
    Functor.isoWhiskerLeft (singularCochainsFunctor R 0)
      ((presheafToSheaf J A).mapCochainComplexShiftIso (-(q : ℤ)))

/-- The sheafified ordinary placement is a genuine signed shift. -/
def sheafifiedSingularCochainsShiftIso
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q : ℕ) :
    (sheafifiedSingularCochainsFunctor R J q).obj P ≅
      ((sheafifiedSingularCochainsFunctor R J 0).obj P)⟦-(q : ℤ)⟧ :=
  (sheafifiedSingularCochainsShiftNatIso R J q).app P

/-- Its occupied shifted term is the sheafification of the original chain term. -/
def sheafifiedSingularCochainsShiftedXIso
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q r : ℕ) :
    (((sheafifiedSingularCochainsFunctor R J 0).obj P)⟦-(q : ℤ)⟧).X ((q : ℤ) - r) ≅
      (presheafToSheaf J A).obj (((singularChainsFunctor R).obj P).X r) :=
  (presheafToSheaf J A).mapIso (singularCochainsShiftedXIso R P q r)

/-- Canonical sheafification retains the exact component factor. -/
theorem sheafifiedSingularCochainsShiftIso_hom_f
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q r : ℕ) :
    (sheafifiedSingularCochainsShiftIso R J P q).hom.f ((q : ℤ) - r) =
      (-1 : ℤ) ^ (q * r) •
        ((sheafifiedSingularCochainsXIso R J P q r).hom ≫
          (sheafifiedSingularCochainsShiftedXIso R J P q r).inv) := by
  change (presheafToSheaf J A).map
    ((singularCochainsShiftIso R P q).hom.f ((q : ℤ) - r)) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  change (presheafToSheaf J A).map
    ((singularCochainsShiftIso R P q).hom.f ((q : ℤ) - r)) =
    (-1 : ℤ) ^ (q * r) •
      ((presheafToSheaf J A).map (singularCochainsXIso R P q r).hom ≫
        (presheafToSheaf J A).map (singularCochainsShiftedXIso R P q r).inv)
  simpa only [Functor.map_zsmul, Functor.map_comp] using
    congrArg (fun f => (presheafToSheaf J A).map f)
      (singularCochainsShiftIso_hom_f R P q r)

/-- The sheafified comparison is a chain map in every integer degree. -/
theorem sheafifiedSingularCochainsShiftIso_comm
    (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A) (q : ℕ) (i j : ℤ) :
    (sheafifiedSingularCochainsShiftIso R J P q).hom.f i ≫
        (((sheafifiedSingularCochainsFunctor R J 0).obj P)⟦-(q : ℤ)⟧).d i j =
      ((sheafifiedSingularCochainsFunctor R J q).obj P).d i j ≫
        (sheafifiedSingularCochainsShiftIso R J P q).hom.f j :=
  (sheafifiedSingularCochainsShiftIso R J P q).hom.comm i j

/-- The sheafified comparison is natural in every original presheaf map. -/
theorem sheafifiedSingularCochainsShiftIso_naturality
    {P Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q) (q : ℕ) :
    (sheafifiedSingularCochainsFunctor R J q).map α ≫
        (sheafifiedSingularCochainsShiftIso R J Q q).hom =
      (sheafifiedSingularCochainsShiftIso R J P q).hom ≫
        (CategoryTheory.shiftFunctor (CochainComplex (Sheaf J A) ℤ) (-(q : ℤ))).map
          ((sheafifiedSingularCochainsFunctor R J 0).map α) :=
  (sheafifiedSingularCochainsShiftNatIso R J q).hom.naturality α

end AlgebraicSimplex
