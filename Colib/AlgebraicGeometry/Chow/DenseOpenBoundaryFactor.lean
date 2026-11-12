/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Factoring a normalized boundary through its actual dense open

This is the unchanged geometric factorization formerly in
`PresheavesWithTransfers/A1Invariant/RationalUnitPrincipalAction`. It is independent
of correspondences, polynomial families and homotopy invariance.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow
open Scheme

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

/-- A whole-boundary ordinary unit representative factors the original boundary
through its genuine open domain, preserving the normalization exactly. -/
theorem denseOpen_boundary_factor {C B : Scheme.{u}} (W : DenseOpen C)
    (i : B ⟶ C) (hBW : ⊤ ≤ i ⁻¹ᵁ W.val) (s : Γ(C, W.val))
    (hs : i.appLE W.val ⊤ hBW s = 1) :
    ∃ b : B ⟶ W.val.toScheme, b ≫ W.val.ι = i ∧
      b.appTop (W.val.topIso.inv s) = 1 := by
  let b := B.topIso.inv ≫ i.resLE W.val ⊤ hBW
  refine ⟨b, ?_, ?_⟩
  · simp [b]
  · change (B.topIso.inv ≫ i.resLE W.val ⊤ hBW).appTop _ = 1
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.comp_apply]
    have hh := ConcreteCategory.congr_hom (arrowResLEAppIso i W.val ⊤ hBW).hom.w
    have h := hh (W.val.topIso.inv s)
    change i.appLE W.val ⊤ hBW (W.val.topIso.hom (W.val.topIso.inv s)) =
      (⊤ : B.Opens).topIso.hom ((i.resLE W.val ⊤ hBW).appTop (W.val.topIso.inv s)) at h
    rw [Iso.inv_hom_id_apply] at h
    have he : B.topIso.inv.appTop = (⊤ : B.Opens).topIso.hom := by
      apply (cancel_mono (⊤ : B.Opens).topIso.inv).mp
      change B.topIso.inv.appTop ≫ B.topIso.hom.appTop = _
      rw [← Scheme.Hom.comp_appTop, B.topIso.hom_inv_id]
      exact (⊤ : B.Opens).topIso.hom_inv_id.symm
    rw [he, ← h, hs]

end AlgebraicGeometry.PrincipalFamilyUnitOpen
