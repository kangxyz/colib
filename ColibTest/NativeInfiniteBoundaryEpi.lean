/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.Iso
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.InfiniteFieldEpi

/-! The native coordinate comparisons and the actual infinite-field boundary maps. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.SmoothSite.Contraction
open AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open AlgebraicGeometry.Scheme.SmoothSite.AffineSectionCoordinates
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
universe u

section FullCoordinates
variable {k : Type u} [Field k]
attribute [local instance] SmoothSite.AffineSectionCoordinates.sectionsAlgebra

example (B : SmoothSite (Spec (.of k))) [IsAffine B.left]
    {E : Scheme.{u}} (q : E ⟶ (affineLineCylinder.obj B).left)
    (a : B.left ⟶ E)
    (H : IsPullback a (𝟙 B.left) q (nativeAffineSection (.of k) B 0).left) :
    IsPullback ((affineIso B).hom.left ≫ a) (𝟙 _)
      (q ≫ (affineLineIso B).inv.left)
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : Γ(B.left, ⊤))))) :=
  affineLineIso_wholeZero_isPullback B q a H

example (R : Type u) [CommRing R] [Algebra k R] [Algebra.Smooth k R] :
    (PolynomialOpenQuotient.SmoothSite.puncturedProductIso (k := k) (R := R)).hom ≫
      Contraction.openInclusion.app (affineSite k R) =
    polynomialPunctureInclusion (k := k) (R := R) ≫
      (lineCylinderIso (k := k) (R := R)).hom :=
  PolynomialOpenQuotient.SmoothSite.puncturedProductIso_open (k := k) (R := R)
end FullCoordinates

section InfiniteField
variable {k : Type u} [Field k] [Infinite k]
  (X : SmoothSite (Spec (.of k)))

example (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    Epi (Boundary.OriginalPresheaf.contractionToBoundary X P) :=
  Boundary.OriginalPresheaf.contractionToBoundary_epi X P hP

example : Boundary.OriginalPresheaf.CanonicalBoundaryEpi k :=
  Boundary.OriginalPresheaf.canonicalBoundaryEpi

example (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) :
    Epi (Boundary.contractionToBoundary X F hF) :=
  Boundary.contractionToBoundary_epi X F hF

example (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) :
    IsIso (Boundary.contractionToBoundary X F hF) :=
  Boundary.contractionToBoundary_isIso X F hF
end InfiniteField
