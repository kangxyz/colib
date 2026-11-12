/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.BoundarySectionEquations

/-! # Original section models through the actual stage refinements

The original module identification is extended by the inverse canonical pullback
comparison. Actual section recovery, and its preservation under a further literal
pullback, are proved without selecting a replacement model or section.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Refine the original model isomorphism along the prescribed original triangle. -/
def refinedSectionModelIso {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (p : W ⟶ Y) (hp : f ≫ g = p) (L : Y.Modules) {M : W.Modules}
    (E : M ≅ (pullback p).obj L) :
    M ≅ (pullback f).obj ((pullback g).obj L) :=
  E ≪≫ (canIso f g p hp L).symm

/-- The actual canonical recovery equation supplied by section descent yields
recovery through the prescribed refined original module isomorphism. -/
theorem refinedSectionModelIso_recovery {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (p : W ⟶ Y) (hp : f ≫ g = p) (L : Y.Modules) {M : W.Modules}
    (E : M ≅ (pullback p).obj L) (s : Γ(M, ⊤)) (t : Γ((pullback g).obj L, ⊤))
    (ht : Hom.app (canHom f g p hp L) ⊤
      (pullbackGlobalSections f ((pullback g).obj L) t) = Hom.app E.hom ⊤ s) :
    Hom.app (refinedSectionModelIso f g p hp L E).hom ⊤ s =
      pullbackGlobalSections f ((pullback g).obj L) t := by
  change Hom.app (canIso f g p hp L).inv ⊤ (Hom.app E.hom ⊤ s) = _
  exact (congrArg (Hom.app (canIso f g p hp L).inv ⊤) ht).symm.trans
    (app_inv_app (canIso f g p hp L) ⊤ _)

/-- A further literal pullback preserves the original section-model recovery. -/
theorem refinedSectionModelIso_pullback_recovery {W X Y : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (p : W ⟶ Y) (hp : f ≫ g = p) (L : Y.Modules)
    {M : W.Modules} (E : M ≅ (pullback p).obj L)
    (s : Γ(M, ⊤)) (t : Γ(L, ⊤))
    (ht : Hom.app E.hom ⊤ s = pullbackGlobalSections p L t) :
    Hom.app (refinedSectionModelIso f g p hp L E).hom ⊤ s =
      pullbackGlobalSections f ((pullback g).obj L) (pullbackGlobalSections g L t) := by
  apply refinedSectionModelIso_recovery f g p hp L E s
  exact (canIso_pullbackGlobalSections f g p hp L t).trans ht.symm

end AlgebraicGeometry.Scheme.Modules
