/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.AffineLineMotivicRepresentative
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.IntegralOmegaSpectrum
public import Colib.CategoryTheory.Prespectrum.Free
public import Mathlib.CategoryTheory.Adjunction.Limits
import Colib.Util.References

/-!
# Cohomology represented by the integral Tate Ω-spectrum

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
integral Ω-spectrum compute reduced motivic cohomology in bidegree `(2q,q)`. -/
@[no_expose, colib_tag "COL-1117"]
def integralMotivicTateOmegaSpectrumHomEquiv (q : ℕ)
    (X : PointedSimplicialPresheaf.{u + 1} Cₖ) :
    ((F q).obj ((Qₖ).obj X) ⟶ (integralMotivicTateOmegaSpectrum k).obj) ≃
      (reducedHypercohomology Cₖ Jₖ (motivicSheafComplex k q) (2 * (q : ℤ))).obj (op X) := by
  let E := (integralMotivicTateOmegaSpectrum k).obj
  have h : E.level q = motivicAffineLineRepresentative k (2 * (q : ℤ)) q := by
    change (integralMotivicTatePrespectrum k).level q = _
    exact integralMotivicTatePrespectrum_level k q
  let e := eqToIso h
  exact ((SequentialPrespectrum.freeAtAdjunction (S := motivicTateSuspension Rₖ) q).homEquiv
    ((Qₖ).obj X) E).trans (e.homToEquiv.trans
      (motivicAffineLineRepresentativeHomEquiv k (2 * (q : ℤ)) q X))

/-- The integral representation sends precomposition by the original free
prespectrum map to restriction on reduced motivic cohomology. -/
@[colib_tag "COL-1117"]
theorem integralMotivicTateOmegaSpectrumHomEquiv_precomp (q : ℕ)
    {X Y : PointedSimplicialPresheaf.{u + 1} Cₖ} (f : X ⟶ Y)
    (a : (F q).obj ((Qₖ).obj Y) ⟶ (integralMotivicTateOmegaSpectrum k).obj) :
    integralMotivicTateOmegaSpectrumHomEquiv k q X ((F q).map ((Qₖ).map f) ≫ a) =
      (reducedHypercohomology Cₖ Jₖ (motivicSheafComplex k q) (2 * (q : ℤ))).map f.op
        (integralMotivicTateOmegaSpectrumHomEquiv k q Y a) := by
  let E := (integralMotivicTateOmegaSpectrum k).obj
  have hE : E.level q = motivicAffineLineRepresentative k (2 * (q : ℤ)) q := by
    change (integralMotivicTatePrespectrum k).level q = _
    exact integralMotivicTatePrespectrum_level k q
  let e := eqToIso hE
  let A := SequentialPrespectrum.freeAtAdjunction (S := motivicTateSuspension Rₖ) q
  let r : (Qₖ).obj Y ⟶ E.level q := A.homEquiv ((Qₖ).obj Y) E a
  let b : (Qₖ).obj X ⟶ E.level q := A.homEquiv ((Qₖ).obj X) E
    ((F q).map ((Qₖ).map f) ≫ a)
  have h : b = (Qₖ).map f ≫ r :=
    A.homEquiv_naturality_left ((Qₖ).map f) a
  change motivicAffineLineRepresentativeHomEquiv k (2 * (q : ℤ)) q X (b ≫ e.hom) =
    (reducedHypercohomology Cₖ Jₖ (motivicSheafComplex k q) (2 * (q : ℤ))).map f.op
      (motivicAffineLineRepresentativeHomEquiv k (2 * (q : ℤ)) q Y (r ≫ e.hom))
  rw [h, Category.assoc]
  exact motivicAffineLineRepresentativeHomEquiv_precomp k (2 * (q : ℤ)) q f (r ≫ e.hom)

/-- For a smooth representable the integral spectrum computes its ordinary motivic cohomology. -/
@[no_expose, colib_tag "COL-1117"]
def integralMotivicTateOmegaSpectrumYonedaHomEquiv (q : ℕ) (U : Cₖ) :
    ((F q).obj ((Qₖ).obj ((liftedSmoothPointedYoneda Sₖ).obj U)) ⟶
      (integralMotivicTateOmegaSpectrum k).obj) ≃ motivicCohomology k (2 * (q : ℤ)) q U :=
  (integralMotivicTateOmegaSpectrumHomEquiv k q ((liftedSmoothPointedYoneda Sₖ).obj U)).trans
    (((reducedHypercohomologyYonedaIso.{w₃, u + 1} Cₖ Jₖ (motivicSheafComplex k q)
      (2 * (q : ℤ))).app (op U)).addCommGroupIsoToAddEquiv.toEquiv)

end AlgebraicGeometry.MotivicHomotopy
