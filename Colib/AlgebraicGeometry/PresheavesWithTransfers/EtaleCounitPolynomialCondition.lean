/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.PolynomialTailToAffineStructural
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction

/-! # Polynomial tails supply the exact algebraically closed counit condition -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open QuadraticIncidence.InfinityChart
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
local instance {K : Type u} [Field K] : IsAffine (base (Spec (.of K))).left :=
  inferInstanceAs (IsAffine (Spec (.of K)))

/-- The exact right side of the actual algebraically-closed counit reduction,
including its original `default` marking and native residue scalar action. -/
theorem counit_separable_condition_of_polynomial_tails
    (K : Type u) [Field K] (P : PresheafWithTransfers.{u + 1} K)
    (hAll : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (d : ℕ),
      PolynomialTailIsomorphisms K Ω ((toPresheaf K).obj P) d) :
    ∀ (X : SmoothSite (Spec (.of K))) [IsAffine X.left]
      (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ξ : Spec (.of Ω) ⟶ X.left),
      IsClosed ({ξ default} : Set X.left) →
        let : Algebra K (X.left.residueField (ξ default)) :=
          (fieldToResidue X.hom (ξ default)).hom.toAlgebra
        Algebra.IsSeparable K (X.left.residueField (ξ default)) →
          IsIso (etaleNeighborhoodValuePullback
            (homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp) :
              X ⟶ base (Spec (.of K))) (ξ := ξ) rfl ((toPresheaf K).obj P)) := by
  intro X _ Ω _ _ ξ _ _ hs
  apply isIso_affine_structural_of_polynomialTailIsomorphisms K Ω ((toPresheaf K).obj P)
    (hAll Ω) X ξ
  exact (congrArg (fun x : X.left =>
    letI : Algebra K (X.left.residueField x) := (fieldToResidue X.hom x).hom.toAlgebra
    Algebra.IsSeparable K (X.left.residueField x))
    (congrArg ξ (Subsingleton.elim (default : Spec (.of Ω))
      (IsLocalRing.closedPoint Ω : Spec (.of Ω))))).mp hs

end AlgebraicGeometry.PresheafWithTransfers
