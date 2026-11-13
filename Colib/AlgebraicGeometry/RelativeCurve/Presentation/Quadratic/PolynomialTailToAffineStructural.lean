/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.PolynomialTailInduction
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.SmoothMarkedPolynomialChart
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodEtaleIsoFactor
public import Colib.AlgebraicGeometry.ResidueField.SeparableDescent
public import Colib.AlgebraicGeometry.Limits.EtalePolynomialCoordinate

/-! # All polynomial tails give the actual affine structural comparison

This reduction uses actual principal charts and native residue scalar maps.
Polynomial-tail isomorphisms are an explicit input, not a claimed rigidity theorem.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
universe u
namespace QuadraticIncidence.InfinityChart
local instance {K : Type u} [Field K] : IsAffine (base (Spec (.of K))).left :=
  inferInstanceAs (IsAffine (Spec (.of K)))

/-- A native separable source marking gives a separable polynomial image. -/
theorem polynomial_chart_mark_residue_separable
    (K Ω : Type u) [Field K] [Field Ω]
    {R : CommRingCat.{u}} {X : Scheme.{u}}
    (s : X ⟶ Spec (.of K)) (j : Spec R ⟶ X) [Etale j]
    (d : ℕ) (q : Spec R ⟶ Spec (.of (MvPolynomial (Fin d) K)))
    (hstruct : q ≫ Spec.map (CommRingCat.ofHom
      (algebraMap K (MvPolynomial (Fin d) K))) = j ≫ s)
    (η : Spec (.of Ω) ⟶ Spec R) (ξ : Spec (.of Ω) ⟶ X) (hη : η ≫ j = ξ)
    (hs : letI := (fieldToResidue s (ξ (IsLocalRing.closedPoint Ω))).hom.toAlgebra
      Algebra.IsSeparable K (X.residueField (ξ (IsLocalRing.closedPoint Ω)))) :
    letI := (fieldToResidue (Spec.map (CommRingCat.ofHom
      (algebraMap K (MvPolynomial (Fin d) K))))
      ((η ≫ q) (IsLocalRing.closedPoint Ω))).hom.toAlgebra
    Algebra.IsSeparable K ((Spec (.of (MvPolynomial (Fin d) K))).residueField
      ((η ≫ q) (IsLocalRing.closedPoint Ω))) := by
  have hsU := isSeparable_residueField_of_etale_mark s j η ξ hη hs
  have hsU' := (congrArg (fun h : Spec R ⟶ Spec (.of K) =>
    letI : Algebra K ((Spec R).residueField (η (IsLocalRing.closedPoint Ω))) :=
      (fieldToResidue h (η (IsLocalRing.closedPoint Ω))).hom.toAlgebra
    Algebra.IsSeparable K ((Spec R).residueField (η (IsLocalRing.closedPoint Ω))))
    hstruct).mpr hsU
  exact isSeparable_residueField_image_of_over_field _ q
    (η (IsLocalRing.closedPoint Ω)) hsU'

/-- Actual smooth coordinates reduce every separable-marked affine object to
polynomial tails on the same K-site. -/
theorem isIso_affine_structural_of_polynomialTailIsomorphisms
    (K Ω : Type u) [Field K] [Field Ω] [IsAlgClosed Ω]
    (Q : (SmoothSite (Spec (.of K)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hAll : ∀ d : ℕ, PolynomialTailIsomorphisms K Ω Q d)
    (X : SmoothSite (Spec (.of K))) [IsAffine X.left]
    (ξ : Spec (.of Ω) ⟶ X.left)
    (hs : letI : Algebra K (X.left.residueField (ξ (IsLocalRing.closedPoint Ω))) :=
        (fieldToResidue X.hom (ξ (IsLocalRing.closedPoint Ω))).hom.toAlgebra
      Algebra.IsSeparable K (X.left.residueField (ξ (IsLocalRing.closedPoint Ω)))) :
    IsIso (etaleNeighborhoodValuePullback
      (homMk X.hom (by exact Category.comp_id _) : X ⟶ base (Spec (.of K)))
      (ξ := ξ) rfl Q) := by
  obtain ⟨R, j, hj, d, q, hq, hstruct, η, hη⟩ :=
    exists_smooth_site_marked_polynomial_chart K Ω X ξ
  let := hj
  let := hq
  let U : SmoothSite (Spec (.of K)) := SmoothSite.mk (j ≫ X.hom)
  let y := Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) K)))
  let Y : SmoothSite (Spec (.of K)) := SmoothSite.mk y
  let : IsAffine U.left := inferInstanceAs (IsAffine (Spec R))
  let : IsAffine Y.left := inferInstanceAs (IsAffine (Spec (.of (MvPolynomial (Fin d) K))))
  let f : U ⟶ X := homMk j rfl
  let c : U ⟶ Y := homMk q hstruct
  let : Etale f.left := inferInstanceAs (Etale j)
  let : Etale c.left := hq
  let gX : X ⟶ base (Spec (.of K)) := homMk X.hom (by exact Category.comp_id _)
  let gY : Y ⟶ base (Spec (.of K)) := homMk Y.hom (by exact Category.comp_id _)
  let θ := η ≫ q
  let ζ := ξ ≫ X.hom
  have hsY := polynomial_chart_mark_residue_separable K Ω X.hom j d q hstruct η ξ hη hs
  have hyOwn : IsIso (etaleNeighborhoodValuePullback gY (ξ := θ) rfl Q) :=
    hAll d K θ hsY
  have hθ : θ ≫ gY.left = ζ := by
    change (η ≫ q) ≫ y = ξ ≫ X.hom
    calc
      (η ≫ q) ≫ y = η ≫ (q ≫ y) := Category.assoc _ _ _
      _ = η ≫ (j ≫ X.hom) := congrArg (fun h => η ≫ h) hstruct
      _ = (η ≫ j) ≫ X.hom := (Category.assoc _ _ _).symm
      _ = ξ ≫ X.hom := congrArg (fun h => h ≫ X.hom) hη
  apply isIso_etaleNeighborhoodValuePullback_of_etale_span
    f c gX gY (by apply MorphismProperty.Over.Hom.ext; exact hstruct)
    η ξ θ ζ hη rfl rfl hθ Q
  exact isIso_etaleNeighborhoodValuePullback_of_target_eq gY θ ζ hθ Q hyOwn

end QuadraticIncidence.InfinityChart
