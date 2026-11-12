/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.CombinedCorrection
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.PolynomialImageTransport

/-!
# The constructed polynomial lift supplies the original boundary image

The two actual corrections transport the original punctured section to an
image witness on the original open arrow.

Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/PolynomialImage.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.RelativeCurve
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
open _root_.AlgebraicGeometry.PolynomialOpenQuotient
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
  (W : EtaleSeparatedFiniteType (SmoothSite.Contraction.affineLineCylinder.obj X).left)
  (R : Type u) [CommRing R] [Algebra k R] [Algebra.Smooth k R]
  {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
  (p : Y ⟶ SmoothSite.lineSite (k := k) (R := R)) [Etale p.left]
  {Z : Scheme.{u}} (z : Z ⟶ Spec (.of (Polynomial R))) (s : Z ⟶ Y.left)
  (w : Spec (.of R))
  (presentation : OriginalEtalePresentation k
    (SmoothSite.lineSite (k := k) (R := R)).hom p.left
    (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R))) z s
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) w))
  (s₀ : Spec (.of R) ⟶ Y.left)
  (hs₀ : s₀ ≫ p.left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))
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

include hP presentation hs₀ hp hmark in
/-- Every original punctured section has an actual open-base image-sieve witness
through the two constructed corrections and the unchanged whole-zero marking. -/
theorem exists_polynomial_boundary_image_neighborhood
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
  have hLift : HasAffinePolynomialTorusLifting R p w P s₀ :=
    OriginalEtalePresentation.exists_original_affine_torus_neighborhood_lifting (k := k)
      R p z s w presentation P hP s₀ hs₀
  exact exists_polynomial_boundary_image_neighborhood_of_lifting (k := k)
    X P W R p w s₀ v₀ e₀ hp hmark hLift d

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
