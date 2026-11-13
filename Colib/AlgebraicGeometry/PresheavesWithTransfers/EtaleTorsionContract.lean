/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction
public import Mathlib.Algebra.Module.Torsion.Basic

/-! # The positive-step torsion condition matches the actual counit reduction -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.PresheafWithTransfers

/-- Natural scalar annihilation on the actual graph objects is precisely the
integer torsion input used by the counit reduction. -/
theorem torsionBy_of_succ_nsmul
    {K : Type u} [Field K] (P : PresheafWithTransfers.{u + 1} K) (n : ℕ)
    (hn : ∀ (V : SmoothSite (Spec (.of K)))
      (z : sections P ((Cor.graphFunctor K).obj V)), (n + 1) • z = 0) :
    ∀ V : SmoothSite (Spec (.of K)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk V)) ((n + 1 : ℕ) : ℤ) := by
  intro V z
  rw [natCast_zsmul]
  exact hn V z

end AlgebraicGeometry.PresheafWithTransfers
