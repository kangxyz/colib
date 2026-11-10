/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Sheafification
public import Colib.Algebra.Homology.Embedding.SignedShift

/-!
# Signed placement for actual transfer singular complexes

Apply the native extension/signed-shift comparison to the genuine transfer
complex and its actual additive sheafification. Every occupied component is
`(-1)^(q*r)` times the canonical term identification; the shifted differential
has its true `(-1)^q` factor.

Adapted from the signed-shift sections of
`Motivic/Transfers/SingularComplex/Presheaf.lean` and `Sheafification.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`. No comparison with the reverted
small-coefficient motivic model is assumed or required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- The exact signed-shift comparison, natural in the transfer presheaf. -/
def singularCochainShiftNatIso (q : ℕ) :
    singularCochainFunctor.{v} (k := k) q ≅
      singularCochainFunctor 0 ⋙ CategoryTheory.shiftFunctor
        (CochainComplex (PresheafWithTransfers.{v} k) ℤ) (-(q : ℤ)) :=
  Functor.isoWhiskerLeft (singularComplexFunctor.{v} (k := k))
    (_root_.HomologicalComplex.ExtensionSignedShift.naturalIso q)

/-- Actual transfer cochains at weight `q` are weight zero shifted by `-q`. -/
def singularCochainShiftIso (P : PresheafWithTransfers.{v} k) (q : ℕ) :
    singularCochainComplex P q ≅ (singularCochainComplex P 0)⟦-(q : ℤ)⟧ :=
  _root_.HomologicalComplex.ExtensionSignedShift.iso (singularComplex P) q

/-- The shifted weight-zero transfer term identified with singular degree `r`. -/
def singularShiftedCochainXIso (P : PresheafWithTransfers.{v} k) (q r : ℕ) :
    ((singularCochainComplex P 0)⟦-(q : ℤ)⟧).X (((q : ℤ) - r)) ≅
      (singularComplex P).X r :=
  _root_.HomologicalComplex.ExtensionSignedShift.shiftedXIso (singularComplex P) q r rfl

/-- Every occupied component has exactly the sign `(-1)^(q*r)`. -/
theorem singularCochainShiftIso_hom_f (P : PresheafWithTransfers.{v} k) (q r : ℕ) :
    (singularCochainShiftIso P q).hom.f (((q : ℤ) - r)) =
      (-1 : ℤ) ^ (q * r) •
        ((singularCochainXIso P q r).hom ≫ (singularShiftedCochainXIso P q r).inv) := by
  change (_root_.HomologicalComplex.ExtensionSignedShift.iso
    (singularComplex P) q).hom.f ((q : ℤ) - r) = _
  rw [_root_.HomologicalComplex.ExtensionSignedShift.iso_hom_f]
  change ((q : ℤ) * r).negOnePow •
      ((singularCochainXIso P q r).hom ≫
        (singularShiftedCochainXIso P q r).inv) = _
  rw [Units.smul_def, ← Nat.cast_mul, Int.coe_negOnePow_natCast]

/-- In weight two every component sign is positive. -/
theorem singularCochainShiftIso_two_hom_f (P : PresheafWithTransfers.{v} k) (r : ℕ) :
    (singularCochainShiftIso P 2).hom.f (((2 : ℤ) - r)) =
      (singularCochainXIso P 2 r).hom ≫ (singularShiftedCochainXIso P 2 r).inv := by
  simpa [pow_mul] using singularCochainShiftIso_hom_f P 2 r


variable (k)
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]

/-- Actual additive transfer sheafification preserves the signed-shift comparison naturally. -/
def singularSheafCochainShiftNatIso (q : ℕ) :
    singularSheafCochainFunctor k q ≅
      singularSheafCochainFunctor k 0 ⋙ CategoryTheory.shiftFunctor
        (CochainComplex (SheafWithTransfers.{u + 1} k) ℤ) (-(q : ℤ)) :=
  Functor.isoWhiskerRight (singularCochainShiftNatIso q)
      ((nisnevichSheafify k).mapHomologicalComplex (ComplexShape.up ℤ)) ≪≫
    Functor.isoWhiskerLeft (singularCochainFunctor 0)
      ((nisnevichSheafify k).mapCochainComplexShiftIso (-(q : ℤ)))

/-- Sheafified transfer cochains in weight `q` are the actual signed shift of weight zero. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/SingularComplex/Sheafification.lean: singularSheafCochainShiftIso"
  "adaptation" "Genuine signed shift of large-coefficient transfer sheaf complexes"]
def singularSheafCochainShiftIso (P : PresheafWithTransfers.{u + 1} k) (q : ℕ) :
    singularSheafCochainComplex k P q ≅ (singularSheafCochainComplex k P 0)⟦-(q : ℤ)⟧ :=
  (singularSheafCochainShiftNatIso k q).app P

/-- The shifted sheaf term identified with sheafification of singular degree `r`. -/
def singularSheafShiftedCochainXIso (P : PresheafWithTransfers.{u + 1} k) (q r : ℕ) :
    ((singularSheafCochainComplex k P 0)⟦-(q : ℤ)⟧).X
        (((q : ℤ) - r)) ≅
      (nisnevichSheafify k).obj ((singularComplex P).X r) :=
  (nisnevichSheafify k).mapIso (singularShiftedCochainXIso P q r)

/-- The sheafified comparison has precisely the original `(-1)^(q*r)` sign. -/
theorem singularSheafCochainShiftIso_hom_f (P : PresheafWithTransfers.{u + 1} k)
    (q r : ℕ) :
    (singularSheafCochainShiftIso k P q).hom.f (((q : ℤ) - r)) =
      (-1 : ℤ) ^ (q * r) •
        ((singularSheafCochainXIso k P q r).hom ≫
          (singularSheafShiftedCochainXIso k P q r).inv) := by
  change (nisnevichSheafify k).map
    ((singularCochainShiftIso P q).hom.f ((q : ℤ) - r)) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  change (nisnevichSheafify k).map
    ((singularCochainShiftIso P q).hom.f ((q : ℤ) - r)) =
    (-1 : ℤ) ^ (q * r) •
      ((nisnevichSheafify k).map (singularCochainXIso P q r).hom ≫
        (nisnevichSheafify k).map (singularShiftedCochainXIso P q r).inv)
  simpa only [Functor.map_zsmul, Functor.map_comp] using
    congrArg (fun f => (nisnevichSheafify k).map f)
      (singularCochainShiftIso_hom_f P q r)

/-- The actual shifted differential has exactly the standard shift sign `(-1)^q`. -/
theorem singularSheafShiftedCochain_d (P : PresheafWithTransfers.{u + 1} k) (q r s : ℕ) :
    ((singularSheafCochainComplex k P 0)⟦-(q : ℤ)⟧).d
        (((q : ℤ) - r)) (((q : ℤ) - s)) =
      (-1 : ℤ) ^ q •
        ((singularSheafShiftedCochainXIso k P q r).hom ≫
          (nisnevichSheafify k).map ((singularComplex P).d r s) ≫
            (singularSheafShiftedCochainXIso k P q s).inv) := by
  calc
    _ = (nisnevichSheafify k).map
        (((singularCochainComplex P 0)⟦-(q : ℤ)⟧).d
          (((q : ℤ) - r)) (((q : ℤ) - s))) := by
      simp only [CochainComplex.shiftFunctor_obj_d', Units.smul_def,
        CategoryTheory.Functor.map_zsmul]
      rfl
    _ = _ := by
      change (nisnevichSheafify k).map
          ((((singularComplex P).extend (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧).d
            ((q : ℤ) - r) ((q : ℤ) - s)) =
        (-1 : ℤ) ^ q •
          ((nisnevichSheafify k).map
              (_root_.HomologicalComplex.ExtensionSignedShift.shiftedXIso (singularComplex P) q r
                  rfl).hom ≫
            (nisnevichSheafify k).map ((singularComplex P).d r s) ≫
              (nisnevichSheafify k).map
                (_root_.HomologicalComplex.ExtensionSignedShift.shiftedXIso (singularComplex P) q s
                    rfl).inv)
      simpa only [Units.smul_def, CategoryTheory.Functor.map_zsmul,
        CategoryTheory.Functor.map_comp, Int.negOnePow_neg, Int.coe_negOnePow_natCast] using
        congrArg (fun f => (nisnevichSheafify k).map f)
          (_root_.HomologicalComplex.ExtensionSignedShift.shifted_d (singularComplex P) q r s)

/-- Weight two retains positive signs after genuine transfer sheafification. -/
theorem singularSheafCochainShiftIso_two_hom_f (P : PresheafWithTransfers.{u + 1} k)
    (r : ℕ) :
    (singularSheafCochainShiftIso k P 2).hom.f (((2 : ℤ) - r)) =
      (singularSheafCochainXIso k P 2 r).hom ≫
        (singularSheafShiftedCochainXIso k P 2 r).inv := by
  simpa [pow_mul] using singularSheafCochainShiftIso_hom_f k P 2 r

end AlgebraicGeometry.PresheafWithTransfers
