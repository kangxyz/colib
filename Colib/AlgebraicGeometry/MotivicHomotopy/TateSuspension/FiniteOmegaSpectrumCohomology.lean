/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.AffineLineMotivicRepresentative
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.FiniteOmegaSpectrum
public import Colib.CategoryTheory.Prespectrum.Free
public import Mathlib.CategoryTheory.Adjunction.Limits
import Colib.Util.References

/-!
# Cohomology represented by the finite Tate Ω-spectrum

The free prespectrum in degree `q` evaluates a map into an Ω-spectrum
at its original level in bidegree `(2q,q)`. The cochain representation
then identifies the resulting map with a reduced cohomology class.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers

universe u w₁ w₂ w₃ w₄ w₅

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w₁} (LargePresheaves k)]
  [HasDerivedCategory.{w₂} (LargeSheaves k)]
  [HasDerivedCategory.{w₃}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₄} ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₅} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Rₖ" => CommRingCat.of k
local notation "Sₖ" => Spec Rₖ
local notation "Cₖ" => SmoothSite Sₖ
local notation "Jₖ" => SmoothSite.nisnevichTopology Sₖ
local notation "Qₖ" => toAffineLineHomotopyCategory Sₖ
local notation "F" q => (SequentialPrespectrum.freeAt (S := motivicTateSuspension Rₖ) q)

/-- Maps from the free Tate prespectrum in degree `q` to the original
finite Ω-spectrum compute reduced cohomology with the multiplication-cone coefficients. -/
@[no_expose, colib_tag "COL-1117"]
def finiteMotivicTateOmegaSpectrumHomEquiv (q n : ℕ)
    (X : PointedSimplicialPresheaf.{u + 1} Cₖ) :
    ((F q).obj ((Qₖ).obj X) ⟶ (finiteMotivicTateOmegaSpectrum k n).obj) ≃
      (reducedHypercohomology Cₖ Jₖ (motivicFiniteSheafComplex k q n)
        (2 * (q : ℤ))).obj (op X) := by
  let E := (finiteMotivicTateOmegaSpectrum k n).obj
  have h : E.level q = motivicFiniteAffineLineRepresentative k (2 * (q : ℤ)) q n := by
    change (finiteMotivicTatePrespectrum k n).level q = _
    exact finiteMotivicTatePrespectrum_level k n q
  let e := eqToIso h
  exact ((SequentialPrespectrum.freeAtAdjunction (S := motivicTateSuspension Rₖ) q).homEquiv
    ((Qₖ).obj X) E).trans (e.homToEquiv.trans
      (motivicFiniteAffineLineRepresentativeHomEquiv k (2 * (q : ℤ)) q n X))

/-- The finite representation sends precomposition to the restriction on
the actual finite coefficient cone. -/
@[colib_tag "COL-1117"]
theorem finiteMotivicTateOmegaSpectrumHomEquiv_precomp (q n : ℕ)
    {X Y : PointedSimplicialPresheaf.{u + 1} Cₖ} (f : X ⟶ Y)
    (a : (F q).obj ((Qₖ).obj Y) ⟶ (finiteMotivicTateOmegaSpectrum k n).obj) :
    finiteMotivicTateOmegaSpectrumHomEquiv k q n X ((F q).map ((Qₖ).map f) ≫ a) =
      (reducedHypercohomology Cₖ Jₖ (motivicFiniteSheafComplex k q n) (2 * (q : ℤ))).map f.op
        (finiteMotivicTateOmegaSpectrumHomEquiv k q n Y a) := by
  let E := (finiteMotivicTateOmegaSpectrum k n).obj
  have hE : E.level q = motivicFiniteAffineLineRepresentative k (2 * (q : ℤ)) q n := by
    change (finiteMotivicTatePrespectrum k n).level q = _
    exact finiteMotivicTatePrespectrum_level k n q
  let e := eqToIso hE
  let A := SequentialPrespectrum.freeAtAdjunction (S := motivicTateSuspension Rₖ) q
  let r : (Qₖ).obj Y ⟶ E.level q := A.homEquiv ((Qₖ).obj Y) E a
  let b : (Qₖ).obj X ⟶ E.level q := A.homEquiv ((Qₖ).obj X) E
    ((F q).map ((Qₖ).map f) ≫ a)
  have h : b = (Qₖ).map f ≫ r :=
    A.homEquiv_naturality_left ((Qₖ).map f) a
  change motivicFiniteAffineLineRepresentativeHomEquiv k (2 * (q : ℤ)) q n X (b ≫ e.hom) =
    (reducedHypercohomology Cₖ Jₖ (motivicFiniteSheafComplex k q n) (2 * (q : ℤ))).map f.op
      (motivicFiniteAffineLineRepresentativeHomEquiv k (2 * (q : ℤ)) q n Y (r ≫ e.hom))
  rw [h, Category.assoc]
  exact motivicFiniteAffineLineRepresentativeHomEquiv_precomp k (2 * (q : ℤ)) q n f (r ≫ e.hom)

/-- For a smooth representable the finite spectrum computes its ordinary motivic cohomology. -/
@[no_expose, colib_tag "COL-1117"]
def finiteMotivicTateOmegaSpectrumYonedaHomEquiv (q n : ℕ) (U : Cₖ) :
    ((F q).obj ((Qₖ).obj ((liftedSmoothPointedYoneda Sₖ).obj U)) ⟶
      (finiteMotivicTateOmegaSpectrum k n).obj) ≃ motivicFiniteCohomology k (2 * (q : ℤ)) q n U :=
  (finiteMotivicTateOmegaSpectrumHomEquiv k q n ((liftedSmoothPointedYoneda Sₖ).obj U)).trans
    (((reducedHypercohomologyYonedaIso.{w₃, u + 1} Cₖ Jₖ (motivicFiniteSheafComplex k q n)
      (2 * (q : ℤ))).app (op U)).addCommGroupIsoToAddEquiv.toEquiv)

end AlgebraicGeometry.MotivicHomotopy
