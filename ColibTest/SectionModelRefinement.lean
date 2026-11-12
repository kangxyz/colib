/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.SectionModelRefinement

/-! # Original model recovery through prescribed stage refinements -/
noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
example {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (p : W ⟶ Y) (hp : f ≫ g = p) (L : Y.Modules) {M : W.Modules}
    (E : M ≅ (pullback p).obj L) (s : Γ(M, ⊤)) (t : Γ((pullback g).obj L, ⊤))
    (ht : Hom.app (canHom f g p hp L) ⊤
      (pullbackGlobalSections f ((pullback g).obj L) t) = Hom.app E.hom ⊤ s) :
    Hom.app (refinedSectionModelIso f g p hp L E).hom ⊤ s =
      pullbackGlobalSections f ((pullback g).obj L) t := refinedSectionModelIso_recovery f g p hp L E s t ht

#print axioms AlgebraicGeometry.Scheme.Modules.refinedSectionModelIso_recovery
example {W X Y : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (p : W ⟶ Y) (hp : f ≫ g = p) (L : Y.Modules)
    {M : W.Modules} (E : M ≅ (pullback p).obj L)
    (s : Γ(M, ⊤)) (t : Γ(L, ⊤))
    (ht : Hom.app E.hom ⊤ s = pullbackGlobalSections p L t) :
    Hom.app (refinedSectionModelIso f g p hp L E).hom ⊤ s =
      pullbackGlobalSections f ((pullback g).obj L) (pullbackGlobalSections g L t) := refinedSectionModelIso_pullback_recovery f g p hp L E s t ht

#print axioms AlgebraicGeometry.Scheme.Modules.refinedSectionModelIso_pullback_recovery
