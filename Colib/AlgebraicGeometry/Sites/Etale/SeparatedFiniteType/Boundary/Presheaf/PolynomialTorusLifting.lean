/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RestrictionDifference.Basic
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.WholeBaseTorus
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks

/-!
# A whole affine marked lift on the polynomial torus

The data are the two original projections, the entire closed mark, the
Cartesian torus square and the signed restriction of original sections.

Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/FinitePolynomialImage.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `ce22a1b5db4fcfe761f9e3150b18cc475d20f1bc`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf

open _root_.AlgebraicGeometry.PolynomialOpenQuotient
open _root_.AlgebraicGeometry.Scheme

/-- A whole affine marked lift on the polynomial torus, with both original projections. -/
def HasAffinePolynomialTorusLifting {K : Type u} [Field K]
    (R : Type u) [CommRing R] [Algebra K R] [Algebra.Smooth K R]
    {Y : SmoothSite (Spec (.of K))}
    (p : Y ⟶ SmoothSite.lineSite (k := K) (R := R)) [Etale p.left]
    (w : Spec (.of R)) (P : PresheafWithTransfers.{u + 1} K)
    (s₀ : Spec (.of R) ⟶ Y.left) : Prop :=
  ∃ (B : SmoothSite (Spec (.of K))) (v : B ⟶ SmoothSite.affineSite K R),
    IsAffine B.left ∧ IsOpenImmersion v.left ∧ w ∈ Set.range v.left ∧
    ∃ (E : SmoothSite (Spec (.of K))) (η : E ⟶ Y)
      (q : E ⟶ SmoothSite.Contraction.affineLineCylinder.obj B) (ζ : B.left ⟶ E.left),
      IsAffine E.left ∧ Etale η.left ∧ Etale q.left ∧
      η ≫ p ≫ (lineCylinderIso (k := K) (R := R)).hom =
        q ≫ SmoothSite.Contraction.affineLineCylinder.map v ∧
      ζ ≫ q.left = (SmoothSite.Contraction.nativeAffineSection (.of K) B 0).left ∧
      ζ ≫ η.left = v.left ≫ s₀ ∧
      ∃ (O : SmoothSite (Spec (.of K))) (α : O ⟶ E)
        (β : O ⟶ SmoothSite.Contraction.torusCylinder.obj B)
        (φ : O ⟶ SmoothSite.etalePullback p (polynomialPunctureInclusion (k := K) (R := R))),
        IsPullback β.left α.left (SmoothSite.Contraction.openInclusion.app B).left q.left ∧
        φ ≫ SmoothSite.etalePullbackFst p (polynomialPunctureInclusion (k := K) (R := R)) =
          α ≫ η ∧ P.HasRestrictionDifferenceLifting φ β α

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
