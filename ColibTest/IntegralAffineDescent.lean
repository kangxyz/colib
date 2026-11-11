/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Smooth.Sheaves.IntegralAffineSheafification
import Colib.AlgebraicGeometry.Sites.Smooth.Units.Sheaf

/-! # Downstream consumers of actual integral affine descent

These examples are pending native elaboration. They test the actual cover,
ordinary sheaf target, large coefficient universe, and canonical unit composite.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite

universe u

variable (k : Type u) [Field k] (X : SmoothSite (Spec (.of k)))

example : IsLocallyNoetherian X.left := inferInstance

example : IsNoetherian X.left := inferInstance

example : IsNormal X.left := inferInstance

example : Finite (componentOpenCover k X).I₀ := inferInstance

example (Z : (componentOpenCover k X).I₀) :
    IsIntegral ((componentOpenCover k X).X Z) := inferInstance

example (i : (integralAffineCover k X).I₀) :
    IsAffine ((integralAffineCover k X).X i) := inferInstance

example (i : (integralAffineCover k X).I₀) :
    IsIntegral ((integralAffineCover k X).X i) := inferInstance

example : integralAffineProperty k X ↔ IsAffine X.left ∧ IsIntegral X.left := Iff.rfl

example : (integralAffineInclusion k).IsCoverDense (nisnevichTopology (Spec (.of k))) :=
  inferInstance

example : Presheaf.IsSheaf Nisnevich.topology Scheme.Γ := globalFunctions_isSheaf

example : Presheaf.IsSheaf (nisnevichTopology (Spec (.of k)))
    (unitsPresheaf (Spec (.of k))) := unitsPresheaf_isSheaf _

example : Presheaf.IsSheaf (nisnevichTopology (Spec (.of k)))
    (largeUnitsPresheaf (Spec (.of k))) := largeUnitsPresheaf_isSheaf _

example : (largeUnitsSheaf (Spec (.of k))).obj = largeUnitsPresheaf (Spec (.of k)) := rfl

example : (largeUnitsSheaf (Spec (.of k))).obj.obj (op X) ≃+
    ULift.{u + 1} (Additive (Γ(X.left, ⊤))ˣ) := largeUnitsSheafSections _ X

variable {F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
  (α : (integralAffineInclusion k).op ⋙ F ⟶
    (integralAffineInclusion k).op ⋙ (largeUnitsSheaf (Spec (.of k))).obj)

example : F ⟶ (largeUnitsSheaf (Spec (.of k))).obj := extendIntegralAffineHom k α

example : (integralAffineInclusion k).op.whiskerLeft (extendIntegralAffineHom k α) = α :=
  extendIntegralAffineHom_restrict k α

example :
    (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj F ⟶
      largeUnitsSheaf (Spec (.of k)) := sheafifyIntegralAffineHom k α

example : toSheafify (nisnevichTopology (Spec (.of k))) F ≫
    (sheafifyIntegralAffineHom k α).hom = extendIntegralAffineHom k α :=
  toSheafify_sheafifyIntegralAffineHom k α

example : (integralAffineInclusion k).op.whiskerLeft
    (toSheafify (nisnevichTopology (Spec (.of k))) F ≫
      (sheafifyIntegralAffineHom k α).hom) = α :=
  sheafifyIntegralAffineHom_restrict k α

example
    (β : (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj F ⟶
      largeUnitsSheaf (Spec (.of k)))
    (hβ : (integralAffineInclusion k).op.whiskerLeft
      (toSheafify (nisnevichTopology (Spec (.of k))) F ≫ β.hom) = α) :
    β = sheafifyIntegralAffineHom k α := sheafifyIntegralAffineHom_unique k α β hβ

example {G H : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}}
    (φ : G ⟶ H)
    (h : ∀ (U : SmoothSite (Spec (.of k))) [IsAffine U.left] [IsIntegral U.left],
      IsIso (φ.hom.app (op U))) : IsIso φ :=
  isIso_of_integral_affine_app k φ h
