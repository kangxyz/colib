/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.ResidueField.SeparableClosedPoint
public import Colib.AlgebraicGeometry.ResidueField.SeparableScalarTower
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.SeparableClosedStructuralMono

/-! # Structural injectivity throughout the finite-coefficient-field induction

Separable residue over the coefficient field implies the actual original-ground
residue condition and closedness. Injectivity therefore needs no separate closedness
hypothesis when the induction changes its finite separable coefficient field.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

local instance {K : Type u} [Field K] : IsAffine (base (Spec (.of K))).left :=
  inferInstanceAs (IsAffine (Spec (.of K)))

/-- Structural injectivity stays on the original K-site while the coefficient field varies. -/
theorem mono_structuralNeighborhoodPullback_of_separable_coefficient
    (K E : Type u) [Field K] [Field E] [Algebra K E] [Algebra.IsSeparable K E]
    (X : SmoothSite (Spec (.of K))) [IsAffine X.left]
    (f : X.left ⟶ Spec (.of E))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap K E)) = X.hom)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X.left)
    (hs : letI := (fieldToResidue f (ξ (IsLocalRing.closedPoint Ω))).hom.toAlgebra
      Algebra.IsSeparable E (X.left.residueField (ξ (IsLocalRing.closedPoint Ω))))
    (F : (SmoothSite (Spec (.of K)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Mono (etaleNeighborhoodValuePullback
      (homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp) :
        X ⟶ base (Spec (.of K))) (ξ := ξ) rfl F) := by
  have hsK : letI : Algebra K (X.left.residueField (ξ (IsLocalRing.closedPoint Ω))) :=
      (fieldToResidue X.hom (ξ (IsLocalRing.closedPoint Ω))).hom.toAlgebra
      Algebra.IsSeparable K (X.left.residueField (ξ (IsLocalRing.closedPoint Ω))) := by
    have h := congrArg (fun g : X.left ⟶ Spec (.of K) =>
      letI : Algebra K (X.left.residueField (ξ (IsLocalRing.closedPoint Ω))) :=
        (fieldToResidue g (ξ (IsLocalRing.closedPoint Ω))).hom.toAlgebra
      Algebra.IsSeparable K (X.left.residueField (ξ (IsLocalRing.closedPoint Ω)))) hf
    exact h.mp (isSeparable_residueField_over_subfield f
      (ξ (IsLocalRing.closedPoint Ω)) hs (K := K))
  have hx := isClosed_of_isSeparable_residueField X.hom (ξ (IsLocalRing.closedPoint Ω)) hsK
  exact mono_structuralNeighborhoodPullback_of_separable_closed X ξ hx hsK F

end AlgebraicGeometry.Scheme.SmoothSite
