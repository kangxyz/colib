/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.CategoryTheory.ExactCategory.BaseChange

/-! # Genuine zero-corner duality in exact categories

The original admissible cofiber squares are exactly the admissible fiber
squares. All kernel and cokernel properties are derived from the original
universal square, with no abelian ambient category required.
-/
/-! Implementation provenance: `Quillen/Aglib/CategoryTheory/ExactCategory/ZeroSquare.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual complexes, maps and independent universes are retained. -/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) {A B Z Q : C}
  {i : A ⟶ B} {z : A ⟶ Z} {q : B ⟶ Q} {s : Z ⟶ Q}

/-- An actual admissible cofiber square is a fiber square on the same arrows. -/
theorem deflation_pullback_of_inflation_pushout_zero
    (hZ : IsZero Z) (hi : E.inflation i) (h : IsPushout i z q s) :
    E.deflation q ∧ IsPullback i z q s := by
  have w : i ≫ q = 0 := h.w.trans (by rw [hZ.eq_of_src s 0, comp_zero])
  let hc : IsColimit (CokernelCofork.ofπ q w) :=
    CokernelCofork.IsColimit.ofπ q w
      (fun k hk => h.desc k 0 (by simp only [comp_zero, hk]))
      (fun k hk => h.inl_desc k 0 _)
      (fun k hk m hm => h.hom_ext (by simpa using hm) (hZ.eq_of_src _ _))
  have hS : E.conflation (ShortComplex.mk i q w) :=
    E.conflation_of_inflation_of_isCokernel hi hc
  refine ⟨E.deflation_of_conflation hS, ?_⟩
  let hk := E.kernel _ hS
  refine IsPullback.mk' h.w ?_ ?_
  · intro T a b hab _
    exact Fork.IsLimit.hom_ext hk hab
  · intro T a b hab
    have ha : a ≫ q = 0 := hab.trans (by rw [hZ.eq_of_src s 0, comp_zero])
    exact ⟨hk.lift (KernelFork.ofι a ha), hk.fac _ WalkingParallelPair.zero,
      hZ.eq_of_tgt _ _⟩

/-- An actual admissible fiber square is a cofiber square on the same arrows. -/
theorem inflation_pushout_of_deflation_pullback_zero
    (hZ : IsZero Z) (hq : E.deflation q) (h : IsPullback i z q s) :
    E.inflation i ∧ IsPushout i z q s := by
  have w : i ≫ q = 0 := h.w.trans (by rw [hZ.eq_of_src s 0, comp_zero])
  let hk : IsLimit (KernelFork.ofι i w) :=
    KernelFork.IsLimit.ofι i w
      (fun k hk => h.lift k 0 (by simp only [zero_comp, hk]))
      (fun k hk => h.lift_fst k 0 _)
      (fun k hk m hm => h.hom_ext (by simpa using hm) (hZ.eq_of_tgt _ _))
  have hS := E.conflation_of_isKernel w hk hq
  refine ⟨E.inflation_of_conflation hS, ?_⟩
  let hc := E.cokernel _ hS
  refine IsPushout.mk' h.w ?_ ?_
  · intro T a b hab _
    exact Cofork.IsColimit.hom_ext hc hab
  · intro T a b hab
    have ha : i ≫ a = 0 := hab.trans (by rw [hZ.eq_of_tgt z 0, zero_comp])
    exact ⟨hc.desc (CokernelCofork.ofπ a ha), hc.fac _ WalkingParallelPair.one,
      hZ.eq_of_src _ _⟩

/-- Exact-category kernel–cokernel duality on the original zero-corner square. -/
theorem inflation_pushout_zero_iff_deflation_pullback (hZ : IsZero Z) :
    (E.inflation i ∧ IsPushout i z q s) ↔ (E.deflation q ∧ IsPullback i z q s) :=
  ⟨fun h => E.deflation_pullback_of_inflation_pushout_zero hZ h.1 h.2,
   fun h => E.inflation_pushout_of_deflation_pullback_zero hZ h.1 h.2⟩

end CategoryTheory.ExactCategory.ExactStructure
