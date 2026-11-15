/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.CoordinateDeformation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateBlowupSmooth
import Mathlib.RingTheory.RingHom.Smooth

/-!
# Smoothness of the coordinate deformation

Over the standard closed affine coordinate embedding, the whole
extended-Rees deformation is an affine space over the original base.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open Stacks.MoreMorphisms

universe u

namespace Stacks.Deformation

variable (R : Type u) [CommRing R] (m n : ℕ)

local notation "A(" R "," m "," n ")" => MvPolynomial (Fin m ⊕ Fin n) R
local notation "B(" R "," m ")" => MvPolynomial (Fin m) R
local notation "P(" R "," m "," n ")" => Polynomial (MvPolynomial (Fin n) (B(R,m)))
local notation "I(" R "," m "," n ")" => coordinateIdeal R m n
local notation "W(" R "," m "," n ")" => topAffineOpen R m n

/-- Reorder the polynomial coordinates into the normal variables over the centre ring. -/
def coordinatePolynomialRingEquiv : A(R,m,n) ≃+* MvPolynomial (Fin n) (B(R,m)) :=
  (MvPolynomial.renameEquiv R (Equiv.sumComm (Fin m) (Fin n))).toRingEquiv.trans
    (MvPolynomial.sumRingEquiv R (Fin n) (Fin m))

private theorem coordinatePolynomialRingEquiv_C (r : R) :
    coordinatePolynomialRingEquiv R m n (MvPolynomial.C r) =
      MvPolynomial.C (MvPolynomial.C r) := by
  simp [coordinatePolynomialRingEquiv, MvPolynomial.sumRingEquiv_C]

/-- A coordinate normal to the centre is an outer polynomial variable. -/
theorem coordinatePolynomialRingEquiv_X (j : Fin n) :
    coordinatePolynomialRingEquiv R m n (MvPolynomial.X (Sum.inr j)) = MvPolynomial.X j := by
  simp [coordinatePolynomialRingEquiv, MvPolynomial.sumRingEquiv_X_inl]

/-- The coordinate presentation on the original global section ring. -/
def coordinateGlobalRingEquiv :
    Γ(Spec (.of A(R,m,n)), ⊤) ≃+* MvPolynomial (Fin n) (B(R,m)) :=
  (gammaEquiv R m n).symm.trans (coordinatePolynomialRingEquiv R m n)

/-- In the original global section ring the centre is cut out by the normal variables. -/
theorem coordinateIdeal_map_coordinateGlobalRingEquiv :
    Ideal.map (coordinateGlobalRingEquiv R m n).toRingHom ((I(R,m,n)).ideal (W(R,m,n))) =
      MvPolynomial.idealOfVars (Fin n) (B(R,m)) := by
  rw [coordinateIdeal_ideal_top, Ideal.map_map]
  have h : (coordinateGlobalRingEquiv R m n).toRingHom.comp
      (gammaEquiv R m n : A(R,m,n) →+* _) =
      (coordinatePolynomialRingEquiv R m n).toRingHom := by
    apply RingHom.ext
    intro a
    exact congrArg (coordinatePolynomialRingEquiv R m n)
      ((gammaEquiv R m n).symm_apply_apply a)
  rw [h, coordinateRingIdeal, Ideal.map_span]
  congr 1
  rw [← Set.range_comp]
  exact congrArg Set.range (funext (coordinatePolynomialRingEquiv_X R m n))

/-- The native coordinate deformation is polynomial in the parameter and normal variables
over the coordinate ring of the centre. -/
def coordinateDeformationGlobalEquiv :
    P(R,m,n) ≃+* Γ(deformationSpace (I(R,m,n)), ⊤) :=
  coordinateDeformationChartEquiv (I(R,m,n)) (W(R,m,n))
    (coordinateGlobalRingEquiv R m n) (coordinateIdeal_map_coordinateGlobalRingEquiv R m n)

local notation "p(" R "," m "," n ")" =>
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* A(R,m,n)))

private theorem coordinateDeformationGlobalEquiv_base (r : R) :
    coordinateDeformationGlobalEquiv R m n (Polynomial.C (MvPolynomial.C (MvPolynomial.C r))) =
      (deformationSpaceToBase (I(R,m,n)) ≫ p(R,m,n)).appTop
        ((ΓSpecIso (.of R)).inv r) := by
  have h : (coordinateGlobalRingEquiv R m n).symm (MvPolynomial.C (MvPolynomial.C r)) =
      gammaEquiv R m n (MvPolynomial.C r) := by
    apply (coordinateGlobalRingEquiv R m n).injective
    rw [RingEquiv.apply_symm_apply]
    change _ = coordinatePolynomialRingEquiv R m n
      ((gammaEquiv R m n).symm (gammaEquiv R m n (MvPolynomial.C r)))
    rw [RingEquiv.symm_apply_apply, coordinatePolynomialRingEquiv_C]
  have hC : (p(R,m,n)).appTop ((ΓSpecIso (.of R)).inv r) =
      gammaEquiv R m n (MvPolynomial.C r) :=
    (ConcreteCategory.congr_hom
      (ΓSpecIso_inv_naturality (CommRingCat.ofHom (MvPolynomial.C : R →+* A(R,m,n)))) r).symm
  change coordinateDeformationChartEquiv (I(R,m,n)) (W(R,m,n))
    (coordinateGlobalRingEquiv R m n) (coordinateIdeal_map_coordinateGlobalRingEquiv R m n)
      (Polynomial.C (MvPolynomial.C (MvPolynomial.C r))) = _
  rw [coordinateDeformationChartEquiv_C_C, h, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, hC]
  rfl

/-- The deformation of the original polynomial coordinate embedding is smooth
over the base of the coordinate affine space. -/
theorem smooth_coordinateDeformation :
    Smooth (deformationSpaceToBase (I(R,m,n)) ≫ p(R,m,n)) := by
  let f := deformationSpaceToBase (I(R,m,n)) ≫ p(R,m,n)
  let : IsAffineHom (deformationSpaceToBase (I(R,m,n))) :=
    Stacks.AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase (extReesAlgebraSheaf (I(R,m,n)))
  let : IsAffine (deformationSpace (I(R,m,n))) :=
    isAffine_of_isAffineHom (deformationSpaceToBase (I(R,m,n)))
  apply (HasRingHomProperty.iff_of_isAffine (P := @Smooth) (f := f)).2
  let e := (ΓSpecIso (.of R)).symm
  apply (RingHom.Smooth.respectsIso.cancel_left_isIso e.hom f.appTop).1
  let E := coordinateDeformationGlobalEquiv R m n
  let c : R →+* P(R,m,n) := Polynomial.C.comp (MvPolynomial.C.comp MvPolynomial.C)
  have hc : @RingHom.Smooth R P(R,m,n) inferInstance inferInstance c := by
    have h₀ : @RingHom.Smooth R B(R,m) inferInstance inferInstance MvPolynomial.C :=
      RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩
    have h₁ : @RingHom.Smooth B(R,m) (MvPolynomial (Fin n) (B(R,m)))
        inferInstance inferInstance MvPolynomial.C :=
      RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩
    have h₂ : @RingHom.Smooth (MvPolynomial (Fin n) (B(R,m))) P(R,m,n)
        inferInstance inferInstance Polynomial.C :=
      RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩
    exact (h₀.comp h₁).comp h₂
  have hmap : f.appTop.hom.comp e.hom.hom = E.toRingHom.comp c := by
    apply RingHom.ext
    intro r
    exact (coordinateDeformationGlobalEquiv_base R m n r).symm
  rw [hmap]
  let a : CommRingCat.of R ⟶ CommRingCat.of (Polynomial (MvPolynomial (Fin n) (B(R,m)))) :=
    CommRingCat.ofHom c
  let e' : CommRingCat.of (Polynomial (MvPolynomial (Fin n) (B(R,m)))) ≅
      Γ(deformationSpace (I(R,m,n)), ⊤) :=
    RingEquiv.toCommRingCatIso (R := Polynomial (MvPolynomial (Fin n) (B(R,m))))
      (S := Γ(deformationSpace (I(R,m,n)), ⊤)) E
  let b := e'.hom
  have hb : IsIso b := e'.isIso_hom
  have hₛ : a.hom.Smooth := hc
  change (a ≫ b).hom.Smooth
  exact (RingHom.Smooth.respectsIso.cancel_right_isIso a b).2 hₛ

end Stacks.Deformation
