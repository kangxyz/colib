/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.TorusChart
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.TorusInversion
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.Coordinates
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Parameters

/-!
# Actual affine coordinates on the torus and its binary product

A map to the native torus from an affine smooth object is represented by
its original global unit, expressed through the canonical spectrum
isomorphism. This comparison preserves inversion. The original binary
torus product is affine and integral over the field.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme SmoothSite

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {k : Type u} [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₖ" => multiplicativeGroupObject Sₖ
local notation "Tₖ" => SmoothSite.product Gₖ Gₖ
local notation "tₖ" => multiplicativeGroupBaseChangeCoordinate Sₖ
set_option quotPrecheck false in
local notation "gₖ" => (multiplicativeGroupBaseChange Sₖ ↘ Sₖ)

/-- The literal binary torus product is affine. -/
theorem torusBinaryProduct_isAffine : IsAffine (Tₖ).left := by
  let : IsAffine (multiplicativeGroupBaseChange Sₖ) :=
    IsAffine.of_isIso (torusFieldChart (k := k)).inv
  change IsAffine (pullback gₖ gₖ)
  infer_instance

/-- The literal binary torus product over a field is integral. -/
theorem torusBinaryProduct_isIntegral : IsIntegral (Tₖ).left := by
  let : Smooth gₖ := inferInstanceAs (Smooth (Gₖ).hom)
  let : GeometricallyIntegral gₖ := inferInstanceAs (GeometricallyIntegral (Gₖ).hom)
  let e : Spec (.of (LaurentPolynomial k)) ≅ multiplicativeGroupBaseChange Sₖ :=
    torusFieldChart (k := k)
  let : IsIntegral (multiplicativeGroupBaseChange Sₖ) := IsIntegral.of_isIso e.hom
  let : IsLocallyNoetherian (multiplicativeGroupBaseChange Sₖ) :=
    LocallyOfFiniteType.isLocallyNoetherian gₖ
  change IsIntegral (pullback gₖ gₖ)
  infer_instance

variable {R : Type u} [CommRing R] [Algebra k R] [Algebra.Smooth k R]

local notation "U" => affineSite k R
set_option quotPrecheck false in
local notation "point(" a ")" =>
  SmoothSite.homMk (X := U) (Y := Gₖ)
    (nativeAffineTorusPoint (U).hom a).left (nativeTorusPoint_over (U).hom (specGlobalUnit a))

/-- The actual coordinate unit of an ordinary affine torus point. -/
def affineUnitOfPoint (a : U ⟶ Gₖ) : Rˣ :=
  Units.map (ΓSpecIso (.of R)).hom.hom.toMonoidHom (Units.map a.left.appTop.hom.toMonoidHom tₖ)

/-- The native affine point of the actual coordinate recovers the original morphism. -/
theorem affineUnitOfPoint_recover (a : U ⟶ Gₖ) : point(affineUnitOfPoint a) = a := by
  apply MorphismProperty.Over.Hom.ext
  let b : Over.mk (U).hom ⟶ Scheme.asOver (multiplicativeGroupBaseChange Sₖ) Sₖ :=
    Over.homMk a.left (MorphismProperty.Over.w a)
  have h : specGlobalUnit (affineUnitOfPoint a) = Units.map b.left.appTop.hom.toMonoidHom tₖ := by
    apply Units.ext
    exact ConcreteCategory.congr_hom (ΓSpecIso (.of R)).hom_inv_id (a.left.appTop (tₖ).val)
  change (nativeTorusPoint (U).hom (specGlobalUnit (affineUnitOfPoint a))).left = b.left
  let eval (v : (Γ(Spec (.of R), ⊤))ˣ) :
      Spec (.of R) ⟶ multiplicativeGroupBaseChange Sₖ := (nativeTorusPoint (U).hom v).left
  exact (congrArg eval h).trans
    (congrArg (fun f => f.left) (nativeTorusPoint_recover (U).hom b))

/-- Composing the native affine point with inversion inverts its actual unit. -/
theorem affineUnitPoint_comp_torusInversion (a : Rˣ) :
    point(a) ≫ torusInversion Sₖ = point(a⁻¹) := by
  apply MorphismProperty.Over.Hom.ext
  have h := nativeTorusPoint_comp_left (Gₖ).hom
    (nativeAffineTorusPoint (U).hom a).left (tₖ⁻¹)
  have hcoord := nativeTorusPoint_coordinate (U).hom (specGlobalUnit a)
  change Units.map (nativeAffineTorusPoint (U).hom a).left.appTop.hom.toMonoidHom tₖ =
    specGlobalUnit a at hcoord
  have hbase : (nativeAffineTorusPoint (U).hom a).left ≫ (Gₖ).hom = (U).hom :=
    nativeTorusPoint_over (U).hom (specGlobalUnit a)
  rw [hbase, map_inv] at h
  let eval (v : (Γ(Spec (.of R), ⊤))ˣ) :
      Spec (.of R) ⟶ multiplicativeGroupBaseChange Sₖ := (nativeTorusPoint (U).hom v⁻¹).left
  have h' := h.symm.trans (congrArg eval hcoord)
  change (nativeAffineTorusPoint (U).hom a).left ≫
      (nativeTorusPoint (Gₖ).hom (tₖ⁻¹)).left =
    (nativeAffineTorusPoint (U).hom a⁻¹).left
  calc
    _ = eval (specGlobalUnit a) := h'
    _ = _ := by simp only [eval, nativeAffineTorusPoint, specGlobalUnit, map_inv]

end AlgebraicGeometry.NativeTorusPolynomial
