/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.BoundaryScalarPullback

/-! # Same original boundary scalar and root-frame witness regression -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
namespace AlgebraicGeometry.Scheme.Modules

example {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D)
    (w : f ≫ g = h ≫ k) (N : D.Modules)
    (e : (pullback g).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (s : Γ(N, ⊤))
    (hs : Hom.app e.hom ⊤ (pullbackGlobalSections g N s) = (1 : Γ(B, ⊤))) :
    Hom.app (pullbackBoundaryTrivialization f g h k w N e).hom ⊤
      (pullbackGlobalSections h _ (pullbackGlobalSections k N s)) = (1 : Γ(A, ⊤)) :=
  pullbackBoundaryTrivialization_section_one f g h k w N e s hs

#print axioms pullbackBoundaryTrivialization_section_one

end AlgebraicGeometry.Scheme.Modules
