/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.ParameterProduct
public import Colib.AlgebraicGeometry.Simplex.PolynomialInterval
public import Colib.AlgebraicGeometry.Simplex.RelativeInterval
import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineSectionNaturality

/-!
# Relative homotopies in the native affine-line parameter

The parameter permutation and the polynomial interval chart convert a
relative cycle on the native affine-line cylinder to the existing prism.
The sign of the endpoint difference follows the actual barycentric chart.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite.Contraction
open AlgebraicTopology.NormalizedMooreComplex
open scoped Simplicial

universe u v

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]
variable (P : (SmoothSite (Spec (CommRingCat.of R)))ᵒᵖ ⥤ AddCommGrpCat.{v})

local notation "A₁" => SmoothSite.additiveGroupObject (Spec (CommRingCat.of R))
set_option quotPrecheck false in
local notation "S(" Q "," V ")" => ((simplicialPresheaf R Q).flip.obj (op V))
set_option quotPrecheck false in
local notation "Δ(" n ")" => (cosimplicialSmoothSite R).obj ⦋n⦌

/-- The actual sections at one and zero of a relative affine-line cycle
differ by a normalized boundary. -/
theorem nativeAffineSection_sub_isNormalizedBoundary (U : SmoothSite (Spec (.of R)))
    (n : ℕ) (x : P.obj (op (affineLineCylinder.obj (SmoothSite.product U Δ(n)))))
    (hx : IsCycle (S((parameterReindex R A₁).obj P,U)) n x) :
    IsBoundary (S(P,U)) n
      (P.map (nativeAffineSection (.of R) (SmoothSite.product U Δ(n)) 1).op x -
        P.map (nativeAffineSection (.of R) (SmoothSite.product U Δ(n)) 0).op x) := by
  let D := Δ(n)
  let E := ((SimplicialObject.whiskering _ _).obj
    ((CategoryTheory.evaluation _ AddCommGrpCat.{v}).obj (op U)))
  let e := nativeAffineCylinderIntervalIso R U
  let g := E.map (simplicialPresheafParameterIso R A₁ P).hom
  let j := (simplicialPresheaf R P).flip.map e.inv.op
  let z := (g ≫ j).app (op ⦋n⦌) x
  have hz := hx.map (g ≫ j)
  have h := intervalEndpoint_sub_isNormalizedBoundary R P U n z hz
  have hpoint (b : Fin 2) :
      ((simplicialPresheaf R P).flip.map (intervalInclusion R U b).op).app (op ⦋n⦌) z =
        P.map (nativeAffineSection (.of R) (SmoothSite.product U D)
          (if b = 0 then 1 else 0)).op x := by
    let m : SmoothSite.product U Δ(1) ⟶ SmoothSite.product U A₁ := e.inv
    have hsection : intervalInclusion R U b ≫ m =
        nativeAffineSection (.of R) U (if b = 0 then 1 else 0) := by
      change intervalInclusion R U b ≫ e.inv = _
      rw [← nativeAffineSection_comp_intervalIso R U b, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    change
      (P.map (SmoothSite.productSwapLast U A₁ D).op ≫
        P.map (SmoothSite.productMap m (𝟙 D)).op ≫
        P.map (SmoothSite.productMap (intervalInclusion R U b) (𝟙 D)).op) x = _
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp,
      ← SmoothSite.productMap_comp, hsection, Category.id_comp,
      productMap_nativeAffineSection_comp_productSwapLast]
    rfl
  have h₀ : (if (0 : Fin 2) = 0 then (1 : R) else 0) = 1 := ite_eq_left rfl
  have h₁ : (if (1 : Fin 2) = 0 then (1 : R) else 0) = 0 := ite_eq_right (by decide)
  rw [hpoint 0, hpoint 1] at h
  rw [h₀, h₁] at h
  exact h

end AlgebraicSimplex
