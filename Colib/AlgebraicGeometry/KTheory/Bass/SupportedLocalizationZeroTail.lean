/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SupportedLocalizationBoundary
public import Colib.AlgebraicGeometry.KTheory.PerfectQcqsConnectiveLocalization

/-!
# The original connective localization tail joins the negative sequence

The actual connective boundary is exact against the same degree-zero forget map used by
Bass recursion. This joins the already defined negative boundary without identifying the
connective boundary with a spectral map in higher positive degrees.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Bass.SupportedLocalization

universe u d

namespace AlgebraicGeometry.Scheme.Bass

variable (A : QuasiCompactOpenPairs.{u}) [CompactSpace A.obj.left]

/-- At degree zero the actual Bass restriction is the connective perfect restriction. -/
theorem supportedLocalization_restriction_zero
    (x : Additive ((perfectComplexesWaldhausen A.obj.right.toRingedSpace).K 0)) :
    negativeKPullback (ObjectProperty.homMk A.obj.hom :
      (⟨A.obj.left, inferInstanceAs (CompactSpace A.obj.left)⟩ : QuasiCompactSchemes.{u}) ⟶
        quasiCompactOpenPairsBase.obj A) 0 x =
      Additive.ofMul (KMap (perfectComplexesRestrictOpenImmersion_isExact A.obj.hom) 0
        x.toMul) := by
  let : CompactSpace A.obj.right := A.property
  change Additive.ofMul (perfectKPullback A.obj.hom 0 x.toMul) = _
  rw [perfectKPullback_eq_restrict]

variable [QuasiSeparatedSpace A.obj.right] [HasDerivedCategory.{d} A.obj.left.Modules]

local instance : CompactSpace ((𝟭 Scheme).obj A.obj.left) :=
  inferInstanceAs (CompactSpace A.obj.left)

local instance : HasDerivedCategory.{d} ((𝟭 Scheme).obj A.obj.left).Modules :=
  inferInstanceAs (HasDerivedCategory.{d} A.obj.left.Modules)

local instance : QuasiSeparatedSpace ((𝟭 Scheme).obj A.obj.right) :=
  inferInstanceAs (QuasiSeparatedSpace A.obj.right)

/-- The actual positive perfect boundary is exact against the literal Bass K₀ forget map. -/
theorem supportedLocalization_positiveBoundary_exact_zero :
    Function.Exact (perfectQcqsConnectingHom A.obj.hom 0).toAdditive
      (supportedNegativeKForget A 0) := by
  let : CompactSpace A.obj.right := A.property
  have h := (perfectQcqs_positiveLongExactSequence A.obj.hom 0).2.1
  intro y
  change perfectSupportedKMap A.obj.hom 0 y.toMul = 1 ↔
    ∃ x : Additive ((perfectComplexesWaldhausen A.obj.left.toRingedSpace).K 1),
      Additive.ofMul (perfectQcqsConnectingHom A.obj.hom 0 x.toMul) = y
  constructor
  · intro hy
    have hm : y.toMul ∈ (perfectQcqsConnectingHom A.obj.hom 0).range := by
      rw [h]
      exact hy
    obtain ⟨x, hx⟩ := hm
    exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩
  · rintro ⟨x, rfl⟩
    have hm : perfectQcqsConnectingHom A.obj.hom 0 x.toMul ∈
        (perfectQcqsConnectingHom A.obj.hom 0).range := ⟨x.toMul, rfl⟩
    rw [h] at hm
    exact hm

/-- The original connective and negative sequences share the unchanged three K₀ groups. -/
theorem supportedLocalization_zeroTail :
    Function.Exact (perfectQcqsConnectingHom A.obj.hom 0).toAdditive
      (supportedNegativeKForget A 0) ∧
    Function.Exact (supportedNegativeKForget A 0)
      (negativeKPullback (ObjectProperty.homMk A.obj.hom :
        (⟨A.obj.left, inferInstanceAs (CompactSpace A.obj.left)⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A) 0) ∧
    Function.Exact
      (negativeKPullback (ObjectProperty.homMk A.obj.hom :
        (⟨A.obj.left, inferInstanceAs (CompactSpace A.obj.left)⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A) 0)
      (supportedNegativeLocalizationConnecting A 0) ∧
    Function.Exact (supportedNegativeLocalizationConnecting A 0)
      (supportedNegativeKForget A 1) :=
  ⟨supportedLocalization_positiveBoundary_exact_zero A,
    by
      let : CompactSpace (localizationSource A).left := localizationSourceCompact A
      let : CompactSpace (localizationTarget A).left := localizationTargetCompact A
      let : IsOpenImmersion (localizationMap A).left := localizationMapOpen A
      let : QuasiSeparatedSpace (localizationTarget A).left :=
        inferInstanceAs (QuasiSeparatedSpace A.obj.right)
      apply Function.Exact.of_ladder_addEquiv_of_exact'
        (identitySupportGroupIso A 0).addCommGroupIsoToAddEquiv
        (identityAmbientGroupIso A 0).addCommGroupIsoToAddEquiv
        (identityOpenGroupIso A 0).addCommGroupIsoToAddEquiv
        (H := boundedAboveFlatCoefficientSupportedNegativeK_localization_exact
          (localizationMap A) 0 identityCoefficient)
      · ext x
        exact (ConcreteCategory.congr_hom (identityForget_square A 0) x).symm
      · ext x
        exact (ConcreteCategory.congr_hom (identityRestriction_square A 0) x).symm,
    supportedNegativeLocalizationConnecting_exact_open A 0,
    supportedNegativeLocalizationConnecting_exact_supported A 0⟩

end AlgebraicGeometry.Scheme.Bass
