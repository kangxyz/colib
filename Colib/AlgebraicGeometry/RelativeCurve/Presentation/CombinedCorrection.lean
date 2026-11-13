/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.AffineCombinedCorrection

/-!
# The original marked torus correction

The affine marked construction supplies the original ambient, torus and
zero-section maps. Forgetting the affine and étale conclusions gives the
same signed lift on the original overlap.

Adapted from `Presentation/CombinedCorrection` at motivic
`a6805c4a87cdfd7717dd7a94039246a167f15380`, blob
`15a28d74410dd5f9ab62725e90d784d2648f486b`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine
open AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine.ZeroNeighborhood

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation

variable {k : Type u} [Field k] (R : Type u) [CommRing R]
  [Algebra k R] [Algebra.Smooth k R]
  {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
  (p : Y ⟶ lineSite (k := k) (R := R)) [Etale p.left]
  {Z : Scheme.{u}} (z : Z ⟶ Spec (.of (Polynomial R))) (s : Z ⟶ Y.left)
  (w : Spec (.of R))
  (e : OriginalEtalePresentation k (lineSite (k := k) (R := R)).hom p.left
    (polynomialPunctureInclusion (k := k) (R := R)).left z s (polynomialZero R w))

local notation "a₁" => polynomialPunctureInclusion (k := k) (R := R)

include e in
/-- Construct both signed corrections and assemble them on one actual original
etale neighborhood. All base, zero, torus and original-overlap maps are retained. -/
theorem exists_original_torus_neighborhood_lifting
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (s₀ : Spec (.of R) ⟶ Y.left) (hs₀ : s₀ ≫ p.left = polynomialZero R) :
    ∃ (B : SmoothSite (Spec (.of k))) (v : B ⟶ affineSite k R),
      IsOpenImmersion v.left ∧ w ∈ Set.range v.left ∧
      ∃ (E : SmoothSite (Spec (.of k))) (η : E ⟶ Y)
        (q : E ⟶ Contraction.affineLineCylinder.obj B) (ζ : B.left ⟶ E.left),
        Etale q.left ∧
        η ≫ p ≫ (lineCylinderIso (k := k) (R := R)).hom =
          q ≫ Contraction.affineLineCylinder.map v ∧
        ζ ≫ q.left = (Contraction.nativeAffineSection (.of k) B 0).left ∧
        ζ ≫ η.left = v.left ≫ s₀ ∧
        ∃ (O : SmoothSite (Spec (.of k))) (α : O ⟶ E)
          (β : O ⟶ Contraction.torusCylinder.obj B)
          (φ : O ⟶ etalePullback p a₁),
          IsPullback β.left α.left (Contraction.openInclusion.app B).left q.left ∧
          φ ≫ etalePullbackFst p a₁ = α ≫ η ∧
          P.HasRestrictionDifferenceLifting φ β α := by
  obtain ⟨B, v, _, hv, hw, E, η, q, ζ, _, _, hq, hbase, hζq, hζη, hLift⟩ :=
    exists_original_affine_torus_neighborhood_lifting (k := k) R p z s w e P hP s₀ hs₀
  exact ⟨B, v, hv, hw, E, η, q, ζ, hq, hbase, hζq, hζη, hLift⟩

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
