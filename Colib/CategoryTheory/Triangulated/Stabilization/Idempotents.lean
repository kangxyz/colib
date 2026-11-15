/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Basic
public import Mathlib.CategoryTheory.Idempotents.Basic

/-! # Splitting idempotents after inversion of an endofunctor

An idempotent on `(A,n)` is an idempotent of the original category, because
inclusion at denominator `n` is fully faithful. Its splitting therefore remains
at that same denominator.
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

variable {C : Type u} [Category.{v} C] (T : C ⥤ C) [T.Full] [T.Faithful]

instance [IsIdempotentComplete C] : IsIdempotentComplete (Stabilization T) where
  idempotents_split X p hp := by
    obtain ⟨A, n⟩ := X
    let F := atLevel T n
    let q : A ⟶ A := F.preimage p
    change (p : F.obj A ⟶ F.obj A) ≫ p = p at hp
    have hqmap : F.map q = (p : F.obj A ⟶ F.obj A) := F.map_preimage p
    have hq : q ≫ q = q := by
      apply F.map_injective
      rw [F.map_comp, hqmap]
      exact hp
    obtain ⟨B, i, e, hie, hei⟩ := IsIdempotentComplete.idempotents_split A q hq
    refine ⟨F.obj B, F.map i, F.map e, ?_, ?_⟩
    · change F.map i ≫ F.map e = 𝟙 (F.obj B)
      rw [← F.map_comp, hie, F.map_id]
    · change F.map e ≫ F.map i = (p : F.obj A ⟶ F.obj A)
      rw [← F.map_comp, hei]
      exact hqmap

end CategoryTheory.Stabilization
