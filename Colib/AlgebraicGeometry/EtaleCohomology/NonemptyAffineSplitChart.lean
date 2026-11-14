/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.SplitLocal
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Nonempty affine splitting charts for finite étale maps -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Stacks.Etale

/-- A finite étale map over a nonempty affine base has a nonempty affine étale
splitting chart. This only asserts existence of one chart, not a cover of the base. -/
theorem exists_nonempty_affine_split_chart
    {K : CommRingCat.{u}} [Nontrivial K] {X : Scheme.{u}}
    (f : X ⟶ Spec K) [IsFinite f] [Etale f] :
    ∃ (R : CommRingCat.{u}) (_ : Nontrivial R) (ψ : K ⟶ R)
      (_ : Etale (Spec.map ψ)), IsSplitCover (pullback.snd f (Spec.map ψ)) := by
  classical
  let s : Spec K := Classical.choice (inferInstance : Nonempty (PrimeSpectrum K))
  obtain ⟨W, q, hq, w, hw, I, hI, e, he⟩ :=
    exists_etale_pullback_iso_sigma f s
  let : Etale q := hq
  have hs : IsSplitCover (pullback.snd f q) := ⟨I, hI, e, he⟩
  obtain ⟨R, j, hj, y, hy⟩ := Scheme.exists_Spec_apply_eq w
  let : IsOpenImmersion j := hj
  have hn : Nontrivial R := PrimeSpectrum.nontrivial y
  have hsplit : IsSplitCover (pullback.snd f (j ≫ q)) :=
    (isSplitCover_pullback_snd_comp f q j).mp (isSplitCover_pullback_snd hs j)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (j ≫ q)
  refine ⟨R, hn, ψ, ?_, ?_⟩
  · rw [hψ]
    infer_instance
  · rwa [hψ]

end Stacks.Etale
