/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.AffineCombinedCorrection
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.FiniteScalarPolynomialCorrection
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.PolynomialOverlap
public import Colib.AlgebraicGeometry.Sites.Smooth.Presentations.LargePrimePolynomial
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.FiniteSeparableExtensionHI

/-! # Finite polynomial corrections on the original boundary

Two actual coprime scalar presentations produce affine corrections over one
original affine base open. Their restricted witnesses retain the original
ambient, full zero sections and signed equations on the actual punctures.
The constructed affine Weil refinement then gives the canonical image witness
on the original open arrow, for the unchanged presheaf with transfers.
-/

/-!
Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/FinitePolynomialImage.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `ce22a1b5db4fcfe761f9e3150b18cc475d20f1bc`. The coefficient maps, full zero schemes and
original puncture projections are retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineSectionCoordinates
open AlgebraicGeometry.Scheme.RelativeCurve
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
open _root_.AlgebraicGeometry.PolynomialOpenQuotient
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance {R L : Type u} [CommRing R] [Field L] [Algebra k R] [Algebra k L]
    [Algebra.Smooth k R] : Algebra.Smooth L (R ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L R)

private theorem produceScalarCorrection
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (R L : Type u) [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [Field L] [Algebra k L] [Module.Finite k L] [Algebra.IsSeparable k L]
    {Y D A : SmoothSite (Spec (.of k))}
    (p : Y ⟶ SmoothSite.lineSite (k := k) (R := R)) [Etale p.left]
    (s₀ : Spec (.of R) ⟶ Y.left)
    (hs₀ : s₀ ≫ p.left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))
    (w : Spec (.of R)) (wL : Spec (.of (R ⊗[k] L)))
    (hu : ∀ v : Spec (.of (R ⊗[k] L)),
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] L))) v = w → v = wL)
    (δ : D ⟶ A) (e₀ : Y ⟶ A)
    (τ : SmoothSite.etalePullback p
      (PolynomialOpenQuotient.SmoothSite.openInclusion (k := k) (Polynomial.X : Polynomial R)) ⟶ D)
    (hτ : τ ≫ δ = SmoothSite.etalePullbackFst p
      (PolynomialOpenQuotient.SmoothSite.openInclusion (k := k) (Polynomial.X : Polynomial R)) ≫ e₀)
    (s : sections P (Cor.mk D))
    (hFY : IsAffine ((SmoothSite.fieldBaseChange (algebraMap k L)).obj Y).left)
    (hpL : Etale ((SmoothSite.fieldBaseChange (algebraMap k L)).map p ≫
      (scalarLineIso k R L).hom).left)
    {Z : Scheme.{u}} (z : Z ⟶ Spec (.of (Polynomial (R ⊗[k] L))))
    (σ : Z ⟶ ((SmoothSite.fieldBaseChange (algebraMap k L)).obj Y).left)
    (presentation : AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation L
      (SmoothSite.lineSite (k := L) (R := R ⊗[k] L)).hom
      ((SmoothSite.fieldBaseChange (algebraMap k L)).map p ≫ (scalarLineIso k R L).hom).left
      (polynomialPunctureInclusion (k := L) (R := R ⊗[k] L)).left z σ
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R ⊗[k] L))) wL))
    (hsL : ((SmoothSite.affineScalarIso k R L).inv ≫
      (SmoothSite.fieldBaseChange (algebraMap k L)).map
        (polynomialZeroLiftSite k R p s₀ hs₀)).left ≫
      ((SmoothSite.fieldBaseChange (algebraMap k L)).map p ≫ (scalarLineIso k R L).hom).left =
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R ⊗[k] L)))) :
    Nonempty (ProducedScalarCorrection P L w (p ≫ lineCylinderIso.hom)
      (polynomialZeroLiftSite k R p s₀ hs₀) δ e₀ s) := by
  let F := SmoothSite.fieldBaseChange (algebraMap k L)
  let pL := F.map p ≫ (scalarLineIso k R L).hom
  let z₀ := polynomialZeroLiftSite k R p s₀ hs₀
  let : IsAffine (F.obj Y).left := hFY
  let : Etale pL.left := hpL
  have hLift : HasAffinePolynomialTorusLifting (R ⊗[k] L) pL wL
      (finiteSeparableExtension L P) ((SmoothSite.affineScalarIso k R L).inv ≫ F.map z₀).left :=
    OriginalEtalePresentation.exists_original_affine_torus_neighborhood_lifting (k := L)
      (R ⊗[k] L) pL z σ wL presentation
        (finiteSeparableExtension L P) (finiteSeparableExtension_isA1Invariant L P hP)
        ((SmoothSite.affineScalarIso k R L).inv ≫ F.map z₀).left hsL
  exact exists_producedScalarCorrection_of_polynomial_lifting (k := k)
    P R L p z₀ w wL hu δ e₀ τ hτ s hpL hLift

/-- Actual coprime scalar presentations give an image witness on an original open
neighborhood. No scalar correction or common-refinement family is supplied. -/
theorem exists_finite_polynomial_boundary_image_neighborhood
    [Finite k] (X : SmoothSite (Spec (.of k)))
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (W : EtaleSeparatedFiniteType (SmoothSite.Contraction.affineLineCylinder.obj X).left)
    (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
    (p : Y ⟶ SmoothSite.lineSite (k := k) (R := R)) [Etale p.left]
    (w : Spec (.of R))
    [(PrimeSpectrum.comap (Polynomial.evalRingHom (0 : R)) w).asIdeal.IsMaximal]
    (s₀ : Spec (.of R) ⟶ Y.left)
    (hs₀ : s₀ ≫ p.left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))
    (H₀ : IsPullback s₀ (𝟙 _) p.left
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))))
    (v₀ : SmoothSite.affineSite k R ⟶
      (toSmoothSite X).obj ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X
        0).left).obj W))
    [IsOpenImmersion v₀.left]
    (e₀ : Y ⟶ (toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).obj W)
    (hp : p ≫ (lineCylinderIso (k := k) (R := R)).hom ≫
      SmoothSite.Contraction.affineLineCylinder.map
        (v₀ ≫ toBase X ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X
          0).left).obj W)) =
      e₀ ≫ toBase (SmoothSite.Contraction.affineLineCylinder.obj X) W)
    (hmark : s₀ ≫ e₀.left = v₀.left ≫
      pullback.fst W.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left)
    (d : ((PresheafWithTransfers.toPresheaf k).obj P).obj (op
      ((toSmoothSite (SmoothSite.Contraction.torusCylinder.obj X)).obj
        ((baseChange (SmoothSite.Contraction.openInclusion.app X).left).obj W)))) :
    ∃ (V : EtaleSeparatedFiniteType X.left)
      (v : V ⟶ (baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left).obj W),
      IsOpenImmersion v.left ∧ v₀.left w ∈ Set.range v.left ∧
      Presheaf.imageSieve (contractionToBoundary X P).hom
        ((presheafBoundaryGenerator ((PresheafWithTransfers.toPresheaf k).obj P)
          (SmoothSite.Contraction.openInclusion.app X)
          (SmoothSite.Contraction.nativeAffineSection (.of k) X 0)).app (op W) d) v := by
  let V₀ := SmoothSite.affineSite k R
  let q₀ := p ≫ (lineCylinderIso (k := k) (R := R)).hom
  let : IsIso (lineCylinderIso (k := k) (R := R)).hom.left :=
    inferInstanceAs (IsIso ((SmoothSite.forgetScheme _).mapIso lineCylinderIso).hom)
  let : Etale q₀.left := inferInstanceAs
    (Etale (p.left ≫ (lineCylinderIso (k := k) (R := R)).hom.left))
  let z₀ := polynomialZeroLiftSite k R p s₀ hs₀
  have hz₀ : z₀ ≫ q₀ = SmoothSite.Contraction.nativeAffineSection (.of k) V₀ 0 := by
    rw [show z₀ ≫ q₀ = (z₀ ≫ p) ≫ lineCylinderIso.hom from (Category.assoc ..).symm,
      polynomialZeroLiftSite_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let δ := (restrictionProjection (SmoothSite.Contraction.openInclusion.app X)).app W
  let τ := polynomialOverlapToPunctured X
    (v₀ ≫ toBase X ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X
      0).left).obj W)) W p e₀ hp
  have hτ : τ ≫ δ = SmoothSite.etalePullbackFst p
      (PolynomialOpenQuotient.SmoothSite.openInclusion (k := k) (Polynomial.X : Polynomial R)) ≫ e₀
          := by
    apply MorphismProperty.Over.Hom.ext
    exact polynomialOverlapToPunctured_fst X _ W p e₀ hp
  obtain ⟨n, m, hn, hm, hnm, hdata⟩ :=
    exists_two_prime_nativePolynomial_presentations k R ℓ w p s₀ hs₀ H₀ 0
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let L₁ := ULift.{u} (FiniteField.Extension k ℓ n)
  let L₂ := ULift.{u} (FiniteField.Extension k ℓ m)
  obtain ⟨hd₁, hY₁, hp₁, w₁, _, hu₁, ⟨e₁⟩, hz₁⟩ := hdata n (Or.inl rfl)
  obtain ⟨hd₂, hY₂, hp₂, w₂, _, hu₂, ⟨e₂⟩, hz₂⟩ := hdata m (Or.inr rfl)
  obtain ⟨c₁⟩ := produceScalarCorrection P hP R L₁ p s₀ hs₀ w w₁ hu₁
    δ e₀ τ hτ d hY₁ hp₁ _ _ e₁ hz₁
  obtain ⟨c₂⟩ := produceScalarCorrection P hP R L₂ p s₀ hs₀ w w₂ hu₂
    δ e₀ τ hτ d hY₂ hp₂ _ _ e₂ hz₂
  have hq₀ : q₀ ≫ SmoothSite.Contraction.affineLineCylinder.map
      (v₀ ≫ toBase X ((baseChange (SmoothSite.Contraction.nativeAffineSection (.of k) X
        0).left).obj W)) = e₀ ≫ toBase (SmoothSite.Contraction.affineLineCylinder.obj X) W := by
    simpa only [q₀, Category.assoc] using hp
  have hmark₀ : z₀.left ≫ e₀.left = v₀.left ≫
      pullback.fst W.hom (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left :=
    hmark
  have hdegrees : (Module.finrank k L₁).Coprime (Module.finrank k L₂) := by
    rw [show Module.finrank k L₁ = n from hd₁, show Module.finrank k L₂ = m from hd₂]
    exact hnm
  exact exists_boundary_image_neighborhood_of_scalar_corrections
    X P W R w q₀ z₀ hz₀ v₀ e₀ hq₀ hmark₀ d c₁ c₂ hdegrees

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
