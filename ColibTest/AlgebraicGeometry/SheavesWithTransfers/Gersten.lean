/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.SheavesWithTransfers.Gersten.PointPurity
import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineSpaceZero
import Colib.AlgebraicGeometry.Sites.Smooth.Injectives
import Mathlib.Algebra.Field.ZMod
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Basic
import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Facts
import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Composition

/-! # Point purity on the affine plane over the two-element field -/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.MotivicHomotopy AlgebraicGeometry.SheafWithTransfers.Gersten

noncomputable section

namespace ColibTest.Gersten

attribute [local instance] specializationOrder

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local notation "𝔽₂" => ZMod 2
local notation "S" => Spec (CommRingCat.of 𝔽₂)

private def basePoint : SmoothSite S := SmoothSite.base S

private def line : SmoothSite S := relativeAffineSpace basePoint 1

private def plane : SmoothSite S := relativeAffineSpace line 1

private def zeroLine : line ⟶ plane := relativeAffineSpaceZeroSection line 1

private def zeroPoint : basePoint ⟶ plane :=
  relativeAffineSpaceZeroSection basePoint 1 ≫ zeroLine

private instance : IsIntegral basePoint.left :=
  inferInstanceAs (IsIntegral (Spec (CommRingCat.of 𝔽₂)))

private instance : IsIntegral line.left := by
  let e := AffineSpace.SpecIso (ULift.{0} (Fin 1)) (CommRingCat.of 𝔽₂)
  exact @IsIntegral.of_isIso _ _ inferInstance e.inv e.isIso_inv

private theorem basePoint_dimension : RelativeDimension basePoint.hom 0 :=
  relativeDimension_zero_of_etale (𝟙 S)

private theorem line_dimension : RelativeDimension line.hom 1 :=
  RelativeDimension.comp_of_flat _ _ (Stacks.Chow.relativeDimension_affineSpaceOver
    basePoint.left 1) basePoint_dimension

private theorem plane_dimension : RelativeDimension plane.hom 2 :=
  RelativeDimension.comp_of_flat _ _ (Stacks.Chow.relativeDimension_affineSpaceOver
    line.left 1) line_dimension

private def lineGeneric : plane.left := zeroLine.left (genericPoint line.left)

private def origin : plane.left := zeroPoint.left (genericPoint basePoint.left)

private theorem lineGeneric_codim : Order.coheight lineGeneric = 1 := by
  let f := plane.hom
  let i := zeroLine.left
  let : IsClosedImmersion i := affineSpaceOrigin_isClosedImmersion line 1
  have h : i ≫ f = line.hom := MorphismProperty.Over.w zeroLine
  let : Smooth (i ≫ f) := h.symm ▸ inferInstanceAs (Smooth line.hom)
  exact codimension_generic_closedImmersion (k := 𝔽₂) f i plane_dimension
    (relativeDimension_transport h.symm line_dimension) _ (genericPoint_spec line.left)

private theorem origin_codim : Order.coheight origin = 2 := by
  let f := plane.hom
  let i := zeroPoint.left
  let j : basePoint ⟶ line := relativeAffineSpaceZeroSection basePoint 1
  let : IsClosedImmersion j.left := affineSpaceOrigin_isClosedImmersion basePoint 1
  let : IsClosedImmersion zeroLine.left := affineSpaceOrigin_isClosedImmersion line 1
  let : IsClosedImmersion i := by
    change IsClosedImmersion (j.left ≫ zeroLine.left)
    infer_instance
  have h : i ≫ f = basePoint.hom := MorphismProperty.Over.w zeroPoint
  let : Smooth (i ≫ f) := h.symm ▸ inferInstanceAs (Smooth basePoint.hom)
  exact codimension_generic_closedImmersion (k := 𝔽₂) f i plane_dimension
    (relativeDimension_transport h.symm basePoint_dimension) _ (genericPoint_spec basePoint.left)

example : ¬ IsClosed ({lineGeneric} : Set plane.left) := by
  intro h
  let j : basePoint.left ⟶ line.left := (relativeAffineSpaceZeroSection basePoint 1).left
  let t : line.left := j (genericPoint basePoint.left)
  have s := (genericPoint_specializes t).map zeroLine.left.continuous
  change lineGeneric ⤳ origin at s
  have hpoint : origin = lineGeneric :=
    Set.mem_singleton_iff.mp (s.mem_closed h (Set.mem_singleton _))
  have hc := congrArg Order.coheight hpoint
  rw [origin_codim, lineGeneric_codim] at hc
  exact (by decide : (2 : ℕ∞) ≠ 1) hc

attribute [local instance] effectiveSupportCoefficientCorSheafify
  effectiveSupportCoefficientSmoothSheafify HasDerivedCategory.standard

local instance gerstenTestTransferAbelian : Abelian (SheafWithTransfers.{1} 𝔽₂) :=
  SheafWithTransfers.abelian 𝔽₂

example (F : SheafWithTransfers.{1} 𝔽₂) (hF : F.obj.IsA1Invariant) :
    IsZero (pointSupportCohomology.{0, 2, 2} 𝔽₂ plane
      (effectiveHICoefficient.{0, 2} 𝔽₂ F hF) 2 lineGeneric) :=
  isZero_pointSupportCohomology_of_ne 𝔽₂ plane lineGeneric F hF lineGeneric_codim 2 (by decide)

example (F : SheafWithTransfers.{1} 𝔽₂) (hF : F.obj.IsA1Invariant) :
    IsZero (pointSupportCohomology.{0, 2, 2} 𝔽₂ plane
      (effectiveHICoefficient.{0, 2} 𝔽₂ F hF) 1 origin) :=
  isZero_pointSupportCohomology_of_ne 𝔽₂ plane origin F hF origin_codim 1 (by decide)

end ColibTest.Gersten

end
