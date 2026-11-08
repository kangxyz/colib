/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The original short exact quotient of a zero pushout

A pushout of a monomorphism along a map to any actual zero object yields the
short exact sequence on the original upper and right arrows. The proof
constructs its genuine cokernel cofork universal property from the original
pushout. Object and morphism universes are independent.

Adapted from `Quillen/Aglib/CategoryTheory/Abelian/ZeroPushout.lean:32-44` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd` using the same native Mathlib objects.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Abelian

/-- A genuine pushout of a monomorphism along a map to an actual zero object
is the original short exact quotient sequence. -/
lemma shortExact_of_mono_pushout_zero {C : Type*} [Category* C] [Abelian C]
    {A B Z Q : C} {i : A ⟶ B} {f : A ⟶ Z} {q : B ⟶ Q} {g : Z ⟶ Q}
    [Mono i] (hZ : IsZero Z) (h : IsPushout i f q g) :
    ∃ w : i ≫ q = 0, (ShortComplex.mk i q w).ShortExact := by
  have w : i ≫ q = 0 := h.w.trans (by rw [hZ.eq_of_src g 0, comp_zero])
  let hc : IsColimit (CokernelCofork.ofπ q w) :=
    CokernelCofork.IsColimit.ofπ q w
      (fun k hk => h.desc k 0 (by simp only [comp_zero, hk]))
      (fun k hk => h.inl_desc k 0 _)
      (fun k hk m hm => h.hom_ext (by simpa using hm) (hZ.eq_of_src _ _))
  exact ⟨w, { exact := (ShortComplex.mk i q w).exact_of_g_is_cokernel hc
              mono_f := inferInstance
              epi_g := Cofork.IsColimit.epi hc }⟩

end CategoryTheory.Abelian
