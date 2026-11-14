/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.DiagonalFirstComparison
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.DiagonalMiddleComparison
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.TwoSummands

/-! # The middle K-map of the diagonal

The base-change weak natural transformation identifies the middle term with the
actual untwisted summand applied to the actual zeroth coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Modules.FlasquePerfect

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => Limits.pullback π π
local notation "p₁" => Limits.pullback.fst π π

local instance : IsProper π := isProper_projectiveSpaceOver 1 X

local notation "I" => inclusion_exact P
local notation "U" => total_exact P
local notation "g₀" => projectiveLineG₀_exact X
local notation "ϕ₀" => projectiveLineFirstSummand_exact X
local notation "m" => (IsExact.comp
  (BoundedBelowPerfect.projectiveLineDiagonalBoundedMiddle_exact X)
  (IsExact.comp (total_exact Q) (perfectPushforward_exact p₁)))

/-- The actual middle term after resolution is the untwisted summand of its direct image. -/
theorem projectiveLineDiagonalMiddle_KMap_apply (n : ℕ)
    (z : (BoundedBelowPerfect.waldhausen P).K n) :
    KMap m n z = KMap ϕ₀ n (KMap g₀ n (KMap U n z)) := by
  have h := KMap_eq_of_weakNatTrans ((g₀).comp ϕ₀) ((I).comp m)
    (projectiveLineDiagonalMiddleComparison X)
    (projectiveLineDiagonalMiddleComparison_weak X) n
  have he := DFunLike.congr_fun h.symm (KMap U n z)
  have hη := DFunLike.congr_fun
    (KMap_eq_of_weakNatTrans (IsExact.id _ _) ((U).comp I) (unit P) (unit_weak P) n) z
  change KMap ((I).comp m) n (KMap U n z) =
    KMap ((g₀).comp ϕ₀) n (KMap U n z) at he
  rw [← KMap_comp_KMap I m n, ← KMap_comp_KMap g₀ ϕ₀ n] at he
  change KMap m n (KMap I n (KMap U n z)) = _ at he
  simp only [KMap_id, MonoidHom.id_apply, ← KMap_comp_KMap U I n,
    MonoidHom.comp_apply] at hη
  simpa only [← hη, MonoidHom.comp_apply] using he

local notation "g₁" => projectiveLineG₁_exact X
local notation "ϕ₁" => projectiveLineSecondSummand_exact X
local notation "f" => (IsExact.comp (BoundedBelowPerfect.projectiveLineDiagonalBoundedFirst_exact X)
  (IsExact.comp (total_exact Q) (perfectPushforward_exact p₁)))

/-- The actual first term after resolution is the negative summand of its twisted direct image. -/
theorem projectiveLineDiagonalFirst_KMap_apply (n : ℕ)
    (z : (BoundedBelowPerfect.waldhausen P).K n) :
    KMap f n z = KMap ϕ₁ n (KMap g₁ n (KMap U n z)) := by
  let e := projectiveLineDiagonalFirstCommon_exact X
  have h₁ := KMap_eq_of_weakNatTrans ((I).comp f) e
    (projectiveLineDiagonalFirstToCommon X)
    (projectiveLineDiagonalFirstToCommon_weak X) n
  have h₂ := KMap_eq_of_weakNatTrans ((g₁).comp ϕ₁) e
    (projectiveLineDiagonalTwistedToCommon X)
    (projectiveLineDiagonalTwistedToCommon_weak X) n
  have he := DFunLike.congr_fun (h₁.trans h₂.symm) (KMap U n z)
  have hη := DFunLike.congr_fun
    (KMap_eq_of_weakNatTrans (IsExact.id _ _) ((U).comp I) (unit P) (unit_weak P) n) z
  change KMap ((I).comp f) n (KMap U n z) =
    KMap ((g₁).comp ϕ₁) n (KMap U n z) at he
  rw [← KMap_comp_KMap I f n, ← KMap_comp_KMap g₁ ϕ₁ n] at he
  change KMap f n (KMap I n (KMap U n z)) = _ at he
  simp only [KMap_id, MonoidHom.id_apply, ← KMap_comp_KMap U I n,
    MonoidHom.comp_apply] at hη
  simpa only [← hη, MonoidHom.comp_apply] using he

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
