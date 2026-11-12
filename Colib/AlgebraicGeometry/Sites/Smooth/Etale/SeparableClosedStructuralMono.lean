/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.ResidueField.FieldPoint
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodEtaleChange
public import Mathlib.RingTheory.Etale.Field

/-! # Structural injectivity at the actual closed separable residue

The residue field is the residue of the original mark. Its finite étale map to
the original base supplies a monic composite of marked-neighborhood pullbacks.
No rigidity, representative surjectivity, or change of the coefficient presheaf
is used. In particular the residue point into X is not asserted to be étale.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

local instance {K : Type u} [Field K] : IsAffine (base (Spec (.of K))).left :=
  inferInstanceAs (IsAffine (Spec (.of K)))

/-- The actual structural pullback is mono at every affine closed point with
separable residue, for an arbitrary presheaf on the original smooth site. -/
theorem mono_structuralNeighborhoodPullback_of_separable_closed
    {K : Type u} [Field K]
    (X : SmoothSite (Spec (.of K))) [IsAffine X.left]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X.left)
    (hx : IsClosed ({ξ (IsLocalRing.closedPoint Ω)} : Set X.left))
    (hsep : letI : Algebra K (X.left.residueField (ξ (IsLocalRing.closedPoint Ω))) :=
      (fieldToResidue X.hom (ξ (IsLocalRing.closedPoint Ω))).hom.toAlgebra
      Algebra.IsSeparable K (X.left.residueField (ξ (IsLocalRing.closedPoint Ω))))
    (F : (SmoothSite (Spec (.of K)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Mono (etaleNeighborhoodValuePullback
      (homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp) :
        X ⟶ base (Spec (.of K))) (ξ := ξ) rfl F) := by
  let x : X.left := ξ (IsLocalRing.closedPoint Ω)
  let κ := X.left.residueField x
  let a : K →+* κ := (fieldToResidue X.hom x).hom
  let : Algebra K κ := a.toAlgebra
  let : Module.Finite K κ := finite_residueField_overField_of_isClosed X.hom x hx
  let : Algebra.IsSeparable K κ := hsep
  let : Algebra.FormallyEtale K κ := Algebra.FormallyEtale.of_isSeparable K κ
  let : Algebra.FinitePresentation K κ :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Etale K κ := ⟨inferInstance, inferInstance⟩
  have hκ : Etale (Spec.map (fieldToResidue X.hom x)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (show (fieldToResidue X.hom x).hom.Etale from
        (RingHom.etale_algebraMap (R := K) (S := κ)).mpr inferInstance)
  let : Etale (Spec.map (fieldToResidue X.hom x)) := hκ
  let R : SmoothSite (Spec (.of K)) := mk (Spec.map (fieldToResidue X.hom x))
  let : IsAffine R.left := inferInstanceAs (IsAffine (Spec κ))
  let : IsAffine (base (Spec (.of K))).left :=
    inferInstanceAs (IsAffine (Spec (.of K)))
  have hr : X.left.fromSpecResidueField x ≫ X.hom =
      Spec.map (fieldToResidue X.hom x) :=
    Scheme.fromSpecResidueField_comp_eq_spec_fieldToResidue X.hom x
  let r : R ⟶ X := homMk (X.left.fromSpecResidueField x) hr
  let g : X ⟶ base (Spec (.of K)) :=
    homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp)
  let θ : Spec (.of Ω) ⟶ R.left :=
    Spec.map (descResidueField (Scheme.stalkClosedPointTo ξ))
  have hθ : θ ≫ r.left = ξ :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X.left ξ
  let : Etale (r ≫ g).left := by
    change Etale (X.left.fromSpecResidueField x ≫ X.hom)
    exact (congrArg Etale hr).mpr hκ
  have ha : θ ≫ (r ≫ g).left = ξ ≫ X.hom :=
    (Category.assoc θ r.left g.left).symm.trans
      (congrArg (fun z => z ≫ g.left) hθ)
  let : IsIso (etaleNeighborhoodValuePullback (r ≫ g) ha F) :=
    (etaleNeighborhoodValueEtaleIso (r ≫ g) ha F).isIso_hom
  have hcomp := etaleNeighborhoodValuePullback_comp r g hθ rfl F
  let : Mono (etaleNeighborhoodValuePullback g (ξ := ξ) rfl F ≫
      etaleNeighborhoodValuePullback r hθ F) := by
    rw [← hcomp]
    exact (inferInstance : Mono (etaleNeighborhoodValuePullback (r ≫ g) ha F))
  exact CategoryTheory.mono_of_mono
    (etaleNeighborhoodValuePullback g (ξ := ξ) rfl F)
    (etaleNeighborhoodValuePullback r hθ F)

end AlgebraicGeometry.Scheme.SmoothSite
