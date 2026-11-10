/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.CoefficientQuotient
public import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceIso

/-!
# The full exterior incidence in the actual parameter quotient

The native incidence maps to the actual coefficient quotient by its common
parameter and its original coefficient-support map. The resulting square with
the original incidence and original coefficient support product is Cartesian.
Every map is the actual native morphism, and the scheme-theoretic incidence is
retained before any Tor or cycle comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

local notation3 (prettyPrint := false) "I'" => nativeExteriorIncidence X Y Z T z w hz hw
local notation3 (prettyPrint := false) "b'" =>
  correspondenceIncidenceToSupportProduct (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
    (SmoothSite.product Z T).hom (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)
local notation3 (prettyPrint := false) "Q" => nativeExteriorParameterDiagonal X Y T z hz Z w hw
local notation3 (prettyPrint := false) "j" =>
  nativeExteriorParameterDiagonalInclusion X Y T z hz Z w hw
local notation3 (prettyPrint := false) "p" =>
  nativeExteriorCoefficientParameterPair X Y T z hz Z w hw
local notation3 (prettyPrint := false) "π" => nativeExteriorIncidenceOriginal X Y Z T z w hz hw
local notation3 (prettyPrint := false) "q" =>
  nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw
local notation3 (prettyPrint := false) "b₀" =>
  correspondenceIncidenceToSupportProduct X.hom Y.hom Z.hom z w

/-- The common parameter and the literal coefficient point give the quotient point. -/
def nativeExteriorIncidenceToCoefficientQuotient : I' ⟶ Q :=
  pullback.lift (nativeExteriorIncidenceFirst X Y Z T z w hz hw ≫ pullback.snd _ _) b' (by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst,
        Category.comp_id, nativeExteriorCoefficientParameterPair_fst,
        correspondenceIncidenceToSupportProduct_fst_assoc,
        nativeExteriorParameter, nativeExteriorIncidenceFirst]
    · simp only [Category.assoc, pullback.diagonal_snd,
        Category.comp_id, nativeExteriorCoefficientParameterPair_snd,
        correspondenceIncidenceToSupportProduct_snd_assoc,
        nativeExteriorParameter]
      simpa only [nativeExteriorIncidenceFirst, nativeExteriorIncidenceSecond, Category.assoc]
        using nativeExteriorIncidence_parameter X Y Z T z w hz hw)

@[reassoc (attr := simp)]
theorem nativeExteriorIncidenceToCoefficientQuotient_parameter :
    nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw ≫
      pullback.fst (pullback.diagonal T.hom) p =
        nativeExteriorIncidenceFirst X Y Z T z w hz hw ≫ pullback.snd _ _ :=
  pullback.lift_fst _ _ _

/-- The quotient factorization preserves the original native support-product inclusion map. -/
@[reassoc (attr := simp)]
theorem nativeExteriorIncidenceToCoefficientQuotient_inclusion :
    nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw ≫ j = b' :=
  pullback.lift_snd _ _ _

/-- Forgetting the parameter agrees in both actual original support coordinates. -/
@[reassoc]
theorem nativeExteriorIncidenceToCoefficientQuotient_projection :
    nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw ≫ q = π ≫ b₀ := by
  apply pullback.hom_ext
    (f := exteriorSupportTargetProjection X Y (integralComponentAt z) ≫ Y.hom)
    (g := exteriorSupportSourceProjection Y Z (integralComponentAt w) ≫ Y.hom)
  · simp only [Category.assoc, correspondenceIncidenceToSupportProduct,
      pullback.mapDesc, pullback.map, pullback.lift_fst, Category.comp_id]
    have h := congrArg
      (fun m => nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw ≫ m)
      (nativeExteriorCoefficientQuotientProjection_fst X Y T z hz Z w hw)
    simpa only [Category.assoc, nativeExteriorIncidenceToCoefficientQuotient_inclusion_assoc,
      correspondenceIncidenceToSupportProduct_fst_assoc,
      nativeExteriorIncidenceOriginal_fst, nativeExteriorIncidenceFirst,
      exteriorSupportTargetProjection, exteriorSupportSourceProjection] using h
  · simp only [Category.assoc, correspondenceIncidenceToSupportProduct,
      pullback.mapDesc, pullback.map, pullback.lift_snd, Category.comp_id]
    have h := congrArg
      (fun m => nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw ≫ m)
      (nativeExteriorCoefficientQuotientProjection_snd X Y T z hz Z w hw)
    simpa only [Category.assoc, nativeExteriorIncidenceToCoefficientQuotient_inclusion_assoc,
      correspondenceIncidenceToSupportProduct_snd_assoc,
      nativeExteriorIncidenceOriginal_snd, nativeExteriorIncidenceSecond,
      exteriorSupportTargetProjection, exteriorSupportSourceProjection] using h

/-- The full exterior incidence is the inverse image of the original incidence under q. -/
theorem nativeExteriorIncidenceQuotient_isPullback :
    IsPullback π (nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw) b₀ q := by
  let c := pullback.fst
    (exteriorSupportTargetProjection X Y (integralComponentAt z) ≫ Y.hom)
    (exteriorSupportSourceProjection Y Z (integralComponentAt w) ≫ Y.hom) ≫
      (exteriorSupportTargetProjection X Y (integralComponentAt z) ≫ Y.hom)
  have hbase : b₀ ≫ c = correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom := by
    dsimp only [c, correspondenceIncidenceToSupportProduct, pullback.mapDesc, pullback.map]
    rw [pullback.lift_fst_assoc]
    simp only [Category.assoc, Category.id_comp, correspondenceIncidenceLeft,
      exteriorSupportTargetProjection, pullback.condition]
  have houter : IsPullback
      (nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw ≫
        pullback.fst (pullback.diagonal T.hom) p) π T.hom (b₀ ≫ c) := by
    rw [nativeExteriorIncidenceToCoefficientQuotient_parameter, hbase]
    exact (nativeExteriorIncidenceOriginal_isPullback X Y Z T z w hz hw).flip
  exact (houter.of_right
    (nativeExteriorIncidenceToCoefficientQuotient_projection X Y Z T z w hz hw)
    (nativeExteriorCoefficientQuotientProjection_isPullback X Y T z hz Z w hw).flip).flip

instance nativeExteriorIncidenceToCoefficientQuotient_isClosedImmersion :
    IsClosedImmersion (nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw) :=
  MorphismProperty.of_isPullback
    (nativeExteriorIncidenceQuotient_isPullback X Y Z T z w hz hw) inferInstance

/-- Point transport for the actual scalar square is retained explicitly. -/
theorem nativeExteriorIncidenceQuotient_point (x : I') :
    b₀ (π x) = q (nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw x) :=
  (congrArg (fun m : I' ⟶ correspondenceSupportProduct X.hom Y.hom Z.hom z w => m x)
    (nativeExteriorIncidenceToCoefficientQuotient_projection X Y Z T z w hz hw)).symm

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/RemainingIncidence.lean:36-95"
  "adaptation" "Full native incidence factorization and exact coefficient projection equality"]
  nativeExteriorIncidenceToCoefficientQuotient
  nativeExteriorIncidenceToCoefficientQuotient_inclusion
  nativeExteriorIncidenceToCoefficientQuotient_projection

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/IncidenceProjection.lean:63-73"
  "adaptation" "Actual native incidence and coefficient quotient form the Cartesian \
  projection square"]
  nativeExteriorIncidenceQuotient_isPullback

end Stacks.Chow
