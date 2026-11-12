/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.ZeroSchemeCartesian

/-! # Whole zero-scheme Cartesian structure-map regression -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Morphisms
universe u
example
    {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (q' : X' ⟶ S')
    (q : X ⟶ S) (b : S' ⟶ S) (h : IsPullback f q' q b)
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    IsFiniteLocallyFree
      ((Stacks.Divisors.zeroScheme X' ((Scheme.Modules.pullback f).obj L)
        (AlgebraicGeometry.pullbackGlobalSections f L s)).subschemeι ≫ q') ↔
      IsFiniteLocallyFree
        (pullback.fst b ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ q)) := zeroScheme_cartesian_isFiniteLocallyFree_iff f q' q b h L s

#print axioms AlgebraicGeometry.idealSheaf_comap_isFiniteLocallyFree_iff
#print axioms AlgebraicGeometry.zeroScheme_cartesian_isFiniteLocallyFree_iff
