/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryRoot

/-! # Target naturality of the original square-pulled boundary frame -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- Transporting the actual target module before or after square pullback gives
exactly the same frame, through the prescribed native comparisons. -/
theorem pullbackBoundaryTrivialization_naturality {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D)
    (w : f ≫ g = h ≫ k) {M L : D.Modules} (α : M ≅ L)
    (τ : (Scheme.Modules.pullback g).obj L ≅ SheafOfModules.unit B.ringCatSheaf) :
    (Scheme.Modules.pullback h).mapIso ((Scheme.Modules.pullback k).mapIso α) ≪≫
      pullbackBoundaryTrivialization f g h k w L τ =
    pullbackBoundaryTrivialization f g h k w M
      ((Scheme.Modules.pullback g).mapIso α ≪≫ τ) := by
  have hn := congrArg
    (fun z => (pullbackSquareIso f g h k w M).symm ≪≫ z ≪≫
      (pullbackSquareIso f g h k w L).symm)
    (pullbackSquareIso_naturality f g h k w α)
  simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl,
    Iso.symm_self_id_assoc] at hn
  have ht := congrArg
    (fun z => z ≪≫ (Scheme.Modules.pullback f).mapIso τ ≪≫ Scheme.Modules.pullbackUnitIso f)
    hn.symm
  dsimp only [pullbackBoundaryTrivialization]
  rw [Functor.mapIso_trans]
  simpa only [Iso.trans_assoc] using ht

end Stacks.AlgebraicGeometry.ModuleLimits
