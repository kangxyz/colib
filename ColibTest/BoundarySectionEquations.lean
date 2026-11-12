/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.BoundarySectionEquations

/-! # Original boundary section square and normalized equation regressions -/
noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
example {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D)
    (w : f ≫ g = h ≫ k) (M : D.Modules)
    (e : (pullback h).obj ((pullback k).obj M) ≅ SheafOfModules.unit A.ringCatSheaf)
    (s : Γ(M, ⊤)) :
    (pullback f).map (unitHomEquivTop ((pullback g).obj M)
        (pullbackGlobalSections g M s)) ≫ (framePullbackIso f g h k w M e).hom =
      (pullback f).map (unitHomEquivTop (SheafOfModules.unit B.ringCatSheaf)
        (1 : Γ(B, ⊤))) ↔
    Hom.app e.hom ⊤
      (pullbackGlobalSections h ((pullback k).obj M) (pullbackGlobalSections k M s)) =
        (1 : Γ(A, ⊤)) := framePullbackIso_originalSection_one_iff f g h k w M e s

example {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D)
    (w : f ≫ g = h ≫ k) (M : D.Modules) (s : Γ(M, ⊤)) :
    Hom.app (pullbackSquareIso f g h k w M).hom ⊤
      (pullbackGlobalSections f ((pullback g).obj M) (pullbackGlobalSections g M s)) =
      pullbackGlobalSections h ((pullback k).obj M) (pullbackGlobalSections k M s) := pullbackSquareIso_pullbackGlobalSections f g h k w M s

#print axioms AlgebraicGeometry.Scheme.Modules.pullback_unitHomEquivTop_one
#print axioms AlgebraicGeometry.Scheme.Modules.framePullbackIso_section_one_iff
#print axioms AlgebraicGeometry.Scheme.Modules.canIso_pullbackGlobalSections
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackSquareIso_pullbackGlobalSections
#print axioms AlgebraicGeometry.Scheme.Modules.framePullbackIso_originalSection_one_iff
