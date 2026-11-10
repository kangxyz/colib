/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.RelativeCohomology.Basic
public import Colib.CategoryTheory.Sites.FreeYonedaPushout
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-!
# Excision for relative Ext of ordinary abelian sheaves

Let a square have vertices `X₁`, `X₂`, `X₃`, `X₄` and arrows `f₁₂`, `f₁₃`,
`f₂₄`, `f₃₄`. Suppose every ordinary abelian sheaf takes its opposite square
to a pullback. The free representing sheaves then form a pushout, so Mathlib's
cokernel theorem identifies the relative sources of `f₁₃` and `f₂₄`.

The isomorphism is the actual cokernel map induced by `(f₁₂, f₃₄)`. Applying
the native Ext bifunctor gives the relative restriction isomorphism in every
natural degree and for every coefficient sheaf. This preserves the original
coefficient and Ext universes. No monomorphism, injective resolution, support
comparison or derived excision triangle is needed for this argument.

## References

* `Motivic/Aglib/CategoryTheory/Sites/SheafCohomology/Relative/Excision.lean:26-44`
  at motivic commit a6805c4a87cdfd7717dd7a94039246a167f15380.
* Mathlib's `isIso_cokernel_map_of_isPushout` supplies the categorical excision
  step; `isPushout_map_freeYoneda` supplies its section-descent hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}] (sq : Square C)

/-- Section descent makes the original map of relative source cokernels an isomorphism. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/CategoryTheory/Sites/SheafCohomology/Relative/Excision.lean:26-32"
  "adaptation" "The original excision cokernel map, evaluated through the native arrow functor"]
theorem isIso_relativeSourceFunctor_map_of_section_descent
    (h : ∀ F : Sheaf J AddCommGrpCat.{max v t}, (sq.op.map F.obj).IsPullback) :
    IsIso ((relativeSourceFunctor.{t} J).map
      (Arrow.homMk sq.f₁₂ sq.f₃₄ sq.fac : Arrow.mk sq.f₁₃ ⟶ Arrow.mk sq.f₂₄)) := by
  rw [relativeSourceFunctor_map]
  exact isIso_cokernel_map_of_isPushout (isPushout_map_freeYoneda J sq h).flip

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- Relative restriction across a section-descent square is an isomorphism in every Ext degree. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/CategoryTheory/Sites/SheafCohomology/Relative/Excision.lean:36-44"
  "adaptation" "The original relative Ext restriction, with no support-cohomology identification"]
theorem isIso_relativeCohomologyFunctor_map_of_section_descent
    (h : ∀ F : Sheaf J AddCommGrpCat.{max v t}, (sq.op.map F.obj).IsPullback)
    (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) :
    IsIso (((relativeCohomologyFunctor.{w, t} J n).obj F).map
      (Arrow.homMk sq.f₁₂ sq.f₃₄ sq.fac : Arrow.mk sq.f₁₃ ⟶ Arrow.mk sq.f₂₄).op) := by
  let := isIso_relativeSourceFunctor_map_of_section_descent J sq h
  change IsIso (((extFunctor n).map ((relativeSourceFunctor.{t} J).map
    (Arrow.homMk sq.f₁₂ sq.f₃₄ sq.fac : Arrow.mk sq.f₁₃ ⟶ Arrow.mk sq.f₂₄)).op).app F)
  infer_instance

end Stacks.Cohomology.FreeYonedaUnivLE
