/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardChartOverlap
public import Colib.AlgebraicGeometry.ProjectiveLine.IntegralLaurentOverlap

/-!
# The integral projective-line overlap and its Laurent coordinate

The actual overlap is the standard open at the product of the homogeneous
variables. Its spectrum identification uses the ordinary Laurent polynomial
ring, with the signed affine coordinate convention fixed by the two restrictions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "Z" => ULift ℤ
local notation "𝒜" => polyGrading Z 1
local notation "x₀" => (MvPolynomial.X 0 : MvPolynomial (Fin 2) Z)
local notation "x₁" => (MvPolynomial.X 1 : MvPolynomial (Fin 2) Z)

/-- The integral overlap is literally the standard open at the product. -/
def integralOverlap : (projectiveSpaceAtUniverse.{u} 1).Opens :=
  Proj.basicOpen 𝒜 (x₀ * x₁)

/-- The same open, viewed as the intersection of the two original charts. -/
theorem integralOverlap_eq :
    integralOverlap.{u} = integralChart 0 ⊓ integralChart 1 :=
  Proj.basicOpen_mul _ _ _

/-- The standard integral overlap is the spectrum of the Laurent polynomial ring. -/
def integralOverlapLaurentIso :
    (integralOverlap.{u}).toScheme ≅ Spec (.of (LaurentPolynomial (ULift.{u} ℤ))) :=
  Proj.basicOpenIsoSpec 𝒜 (x₀ * x₁)
    (SetLike.mul_mem_graded (X_mem_one Z 1 0) (X_mem_one Z 1 1)) (by decide) ≪≫
    Scheme.Spec.mapIso (integralLaurentEquiv Z).toCommRingCatIso.op

/-- The positive integral overlap immersion. -/
def integralOverlapToPositive :
    (integralOverlap.{u}).toScheme ⟶ (integralChart.{u} 0).toScheme :=
  (projectiveSpaceAtUniverse 1).homOfLE (integralOverlap_eq.trans_le inf_le_left)

/-- The negative integral overlap immersion. -/
def integralOverlapToNegative :
    (integralOverlap.{u}).toScheme ⟶ (integralChart.{u} 1).toScheme :=
  (projectiveSpaceAtUniverse 1).homOfLE (integralOverlap_eq.trans_le inf_le_right)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual chart map is the spectrum of its polynomial coordinate map. -/
theorem integralChartPolynomialIso_hom (i : Fin 2) :
    (integralChartPolynomialIso.{u} i).hom =
      Proj.basicOpenToSpec 𝒜 (MvPolynomial.X i) ≫
        Spec.map (CommRingCat.ofHom
          (((MvPolynomial.uniqueAlgEquiv Z (Fin 1)).symm.toRingEquiv.trans
            ((MvPolynomial.renameEquiv Z (finSuccAboveEquiv i)).toRingEquiv.trans
              (chartEquiv Z 1 i))).toRingHom)) := by
  change (Proj.basicOpenToSpec 𝒜 (MvPolynomial.X i) ≫
    Spec.map (CommRingCat.ofHom ((MvPolynomial.renameEquiv Z
      (finSuccAboveEquiv i)).toRingEquiv.trans (chartEquiv Z 1 i)).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.uniqueAlgEquiv Z (Fin 1)).symm.toRingHom) = _
  rw [Category.assoc, ← Spec.map_comp]
  rfl

set_option maxHeartbeats 800000 in
-- Elaborating the original Proj and spectrum isomorphisms exposes both scheme structures.
set_option backward.isDefEq.respectTransparency false in
/-- The positive overlap immersion on the canonical charts gives the actual Laurent arrow. -/
theorem integralOverlapToPositive_polynomial :
    integralOverlapToPositive.{u} ≫ (integralChartPolynomialIso 0).hom =
      integralOverlapLaurentIso.hom ≫ laurentToPolynomial (CommRingCat.of (ULift.{u} ℤ)) := by
  rw [integralChartPolynomialIso_hom]
  change (Proj 𝒜).homOfLE (Proj.basicOpen_mono 𝒜 x₀ (x₀ * x₁)
      ⟨x₁, rfl⟩) ≫
      (Proj.basicOpenToSpec 𝒜 x₀ ≫
        Spec.map (CommRingCat.ofHom (positiveCoordinateEquiv Z).toRingHom)) =
    (Proj.basicOpenToSpec 𝒜 (x₀ * x₁) ≫
      Spec.map (CommRingCat.ofHom (integralLaurentEquiv Z).toRingHom)) ≫
      laurentToPolynomial (CommRingCat.of (ULift.{u} ℤ))
  rw [← Proj.basicOpenToSpec_SpecMap_awayMap_assoc 𝒜 (X_mem_one Z 1 1) rfl]
  simp only [laurentToPolynomial, Category.assoc, ← Spec.map_comp]
  apply congrArg (fun f => Proj.basicOpenToSpec 𝒜 (x₀ * x₁) ≫ Spec.map f)
  exact congrArg CommRingCat.ofHom (integralLaurentEquiv_positiveLeg Z).symm


set_option maxHeartbeats 800000 in
-- Elaborating the original Proj and spectrum isomorphisms exposes both scheme structures.
set_option backward.isDefEq.respectTransparency false in
/-- The inverse overlap immersion on the canonical charts gives the actual inverse Laurent arrow. -/
theorem integralOverlapToNegative_polynomial :
    integralOverlapToNegative.{u} ≫ (integralChartPolynomialIso 1).hom =
      integralOverlapLaurentIso.hom ≫ laurentMinus (CommRingCat.of (ULift.{u} ℤ)) := by
  rw [integralChartPolynomialIso_hom]
  change (Proj 𝒜).homOfLE (Proj.basicOpen_mono 𝒜 x₁ (x₀ * x₁)
      ⟨x₀, (mul_comm x₀ x₁)⟩) ≫
      (Proj.basicOpenToSpec 𝒜 x₁ ≫
        Spec.map (CommRingCat.ofHom (inverseCoordinateEquiv Z).toRingHom)) =
    (Proj.basicOpenToSpec 𝒜 (x₀ * x₁) ≫
      Spec.map (CommRingCat.ofHom (integralLaurentEquiv Z).toRingHom)) ≫
      laurentMinus (CommRingCat.of (ULift.{u} ℤ))
  rw [← Proj.basicOpenToSpec_SpecMap_awayMap_assoc 𝒜 (X_mem_one Z 1 0) (mul_comm x₀ x₁)]
  simp only [laurentMinus, Category.assoc, ← Spec.map_comp]
  apply congrArg (fun f => Proj.basicOpenToSpec 𝒜 (x₀ * x₁) ≫ Spec.map f)
  exact congrArg CommRingCat.ofHom (integralLaurentEquiv_inverseLeg Z).symm


end AlgebraicGeometry.Scheme.ProjectiveLine
