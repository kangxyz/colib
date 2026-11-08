/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-!
# Exact functors preserve the native snake connecting morphism

Apply an additive exact functor to the four original short complexes of a
native `ShortComplex.SnakeInput`. Its kernel and cokernel assertions are
transported through the three native projections. The resulting snake input
has the original images as all its rows and vertical morphisms.

The comparison of connecting morphisms is proved on the image of the native
pullback epimorphism. The native characterization `SnakeInput.δ_eq` then
retains the connecting-map sign. No alternative snake construction is used.
The snake-lemma construction is the one in pinned Mathlib; exactness is stated
as preservation of finite limits and finite colimits.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.ShortComplex.SnakeInput

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable (S : SnakeInput C) (F : C ⥤ D) [F.Additive]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The original four rows and vertical maps, acted on by an exact functor. -/
def map : SnakeInput D where
  L₀ := S.L₀.map F
  L₁ := S.L₁.map F
  L₂ := S.L₂.map F
  L₃ := S.L₃.map F
  v₀₁ := F.mapShortComplex.map S.v₀₁
  v₁₂ := F.mapShortComplex.map S.v₁₂
  v₂₃ := F.mapShortComplex.map S.v₂₃
  w₀₂ := by
    rw [← F.mapShortComplex.map_comp, S.w₀₂]
    ext <;> simp
  w₁₃ := by
    rw [← F.mapShortComplex.map_comp, S.w₁₃]
    ext <;> simp
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ
    · exact (KernelFork.isLimitMapConeEquiv _ _).symm
        (isLimitForkMapOfIsLimit' F S.w₀₂_τ₁ S.h₀τ₁)
    · exact (KernelFork.isLimitMapConeEquiv _ _).symm
        (isLimitForkMapOfIsLimit' F S.w₀₂_τ₂ S.h₀τ₂)
    · exact (KernelFork.isLimitMapConeEquiv _ _).symm
        (isLimitForkMapOfIsLimit' F S.w₀₂_τ₃ S.h₀τ₃)
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ
    · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (isColimitCoforkMapOfIsColimit' F S.w₁₃_τ₁ S.h₃τ₁)
    · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (isColimitCoforkMapOfIsColimit' F S.w₁₃_τ₂ S.h₃τ₂)
    · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (isColimitCoforkMapOfIsColimit' F S.w₁₃_τ₃ S.h₃τ₃)
  L₁_exact := S.L₁_exact.map F
  epi_L₁_g := by change Epi (F.map S.L₁.g); infer_instance
  L₂_exact := S.L₂_exact.map F
  mono_L₂_f := by change Mono (F.map S.L₂.f); infer_instance

/-- Exact functors carry the native connecting map to the native connecting map. -/
theorem map_δ : (S.map F).δ = F.map S.δ := by
  have : Epi (F.map S.L₀'.g) := inferInstance
  apply (cancel_epi (F.map S.L₀'.g)).1
  change F.map (pullback.snd S.L₁.g S.v₀₁.τ₃) ≫ (S.map F).δ =
    F.map (pullback.snd S.L₁.g S.v₀₁.τ₃) ≫ F.map S.δ
  have hδ := (S.map F).δ_eq
    (F.map (pullback.snd S.L₁.g S.v₀₁.τ₃))
    (F.map (pullback.fst S.L₁.g S.v₀₁.τ₃)) (F.map S.φ₁)
    (by
      change F.map (pullback.fst S.L₁.g S.v₀₁.τ₃) ≫ F.map S.L₁.g =
        F.map (pullback.snd S.L₁.g S.v₀₁.τ₃) ≫ F.map S.v₀₁.τ₃
      rw [← F.map_comp, ← F.map_comp, pullback.condition])
    (by
      change F.map S.φ₁ ≫ F.map S.L₂.f =
        F.map (pullback.fst S.L₁.g S.v₀₁.τ₃) ≫ F.map S.v₁₂.τ₂
      rw [← F.map_comp, ← F.map_comp, S.φ₁_L₂_f]
      rfl)
  change F.map (pullback.snd S.L₁.g S.v₀₁.τ₃) ≫ (S.map F).δ =
    F.map S.φ₁ ≫ F.map S.v₂₃.τ₁ at hδ
  have hmap : F.map (pullback.snd S.L₁.g S.v₀₁.τ₃) ≫ F.map S.δ =
      F.map S.φ₁ ≫ F.map S.v₂₃.τ₁ := by
    rw [← F.map_comp, ← F.map_comp, S.snd_δ]
    rfl
  exact hδ.trans hmap.symm

end CategoryTheory.ShortComplex.SnakeInput
