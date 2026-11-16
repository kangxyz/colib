/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalRecognition
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFactorization

/-! # The zero scheme of the projective-line determinant

The factorization criterion uses the actual pullback of the determinant section. It detects
scheme-theoretic factorization, not just membership of the underlying vanishing set.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTwistTensorPow Stacks.Ample

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => pullback π π

instance projectiveLineDiagonalPositiveTwist_isInvertibleModule :
    IsInvertibleModule Q (projectiveLineDiagonalPositiveTwist X) := by
  have : IsInvertibleModule Q (projectiveLineFirstPositiveTwist X) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (pullback.fst π π) _
  have : IsInvertibleModule Q (projectiveLineSecondPositiveTwist X) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (pullback.snd π π) _
  exact Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules Q _ _

instance projectiveLineDiagonalPositiveTwist_isInvertible :
    SheafOfModules.IsInvertible (Q).sheaf.obj (Q).ringCatSheaf.property
      (projectiveLineDiagonalPositiveTwist X) :=
  Stacks.RelativeVeryAmple.stacksIsInvertible Q _

/-- The closed subscheme cut out by the alternating determinant section. -/
abbrev projectiveLineDeterminantIdeal : (Q).IdealSheafData :=
  Stacks.Divisors.zeroScheme Q (projectiveLineDiagonalPositiveTwist X)
    (projectiveLineDiagonalDeterminant X)

/-- The determinant vanishes precisely on test maps factoring through its closed subscheme. -/
theorem projectiveLineDiagonalDeterminant_pullback_eq_zero_iff {T : Scheme.{u}}
    (g : T ⟶ Q) :
    pullbackGlobalSections g (projectiveLineDiagonalPositiveTwist X)
        (projectiveLineDiagonalDeterminant X) = 0 ↔
      ∃ h : T ⟶ (projectiveLineDeterminantIdeal X).subscheme,
        h ≫ (projectiveLineDeterminantIdeal X).subschemeι = g :=
  Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme Q _ _ g

/-- Equality of the two projections is exactly factorization through the actual diagonal. -/
theorem projectiveLine_factorsThrough_diagonal_iff {T : Scheme.{u}} (g : T ⟶ Q) :
    (∃ h : T ⟶ P, h ≫ pullback.diagonal π = g) ↔
      g ≫ pullback.fst π π = g ≫ pullback.snd π π := by
  constructor
  · rintro ⟨h, rfl⟩
    simp
  · intro hg
    refine ⟨g ≫ pullback.fst π π, pullback.hom_ext ?_ ?_⟩
    · simp
    · simpa using hg

/-- The determinant defines the scheme-theoretic relative diagonal. -/
theorem projectiveLineDeterminantIdeal_eq_diagonal :
    projectiveLineDeterminantIdeal X = (pullback.diagonal π).ker := by
  let I := projectiveLineDeterminantIdeal X
  refine le_antisymm ?_ ?_
  · rw [← _root_.AlgebraicGeometry.factorsThrough_ideal_iff_ideal_le_ker]
    apply (projectiveLineDiagonalDeterminant_pullback_eq_zero_iff X _).mp
    apply (projectiveLineDiagonalDeterminant_pullback_eq_zero_iff_projections X _).mpr
    simp
  · have hzero := (projectiveLineDiagonalDeterminant_pullback_eq_zero_iff X I.subschemeι).mpr
      ⟨𝟙 _, Category.id_comp _⟩
    have hproj :=
      (projectiveLineDiagonalDeterminant_pullback_eq_zero_iff_projections X _).mp hzero
    obtain ⟨h, hh⟩ := (projectiveLine_factorsThrough_diagonal_iff X _).mpr hproj
    simpa only [hh, IdealSheafData.ker_subschemeι] using
      h.le_ker_comp (pullback.diagonal π)

end AlgebraicGeometry.Scheme
