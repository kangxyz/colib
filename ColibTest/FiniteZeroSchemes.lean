/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.FiniteZeroSchemes

/-! # Actual finite locally free zero schemes descend from a scheme limit

The section and its invertible module are fixed at a stage. The hypotheses concern
the whole zero scheme of their literal pullback to the limit. Native zero-scheme
base change and native finite-locally-free descent produce the same property at a
later stage. No reduced support or continuity certificate replaces the zero scheme.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow Stacks.Divisors
open Stacks.Morphisms

universe u v w

namespace AlgebraicGeometry

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

example
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : I) [IsNoetherian (D.obj i)]
    {X : Scheme.{u}} [IsNoetherian X] (q : X ⟶ D.obj i) [LocallyOfFiniteType q]
    {κ : Type*} [Finite κ] (L : κ → X.Modules)
    [∀ a, SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L a)]
    (s : ∀ a, Γ(L a, ⊤))
    (h : ∀ a, IsFiniteLocallyFree
      ((zeroScheme (pullback (c.π.app i) q)
        ((Scheme.Modules.pullback (pullback.snd (c.π.app i) q)).obj (L a))
        (pullbackGlobalSections (pullback.snd (c.π.app i) q) (L a) (s a))).subschemeι ≫
          pullback.fst (c.π.app i) q)) :
    ∃ (j : I) (f : j ⟶ i), ∀ a, IsFiniteLocallyFree
      ((zeroScheme (pullback (D.map f) q)
        ((Scheme.Modules.pullback (pullback.snd (D.map f) q)).obj (L a))
        (pullbackGlobalSections (pullback.snd (D.map f) q) (L a) (s a))).subschemeι ≫
          pullback.fst (D.map f) q) := by
  exact exists_zeroSchemes_isFiniteLocallyFree_of_isLimit_finite D c hc i q L s h

end AlgebraicGeometry

#print axioms AlgebraicGeometry.zeroSchemeBaseChange_finiteLocallyFree_iff
#print axioms AlgebraicGeometry.exists_zeroScheme_isFiniteLocallyFree_of_isLimit
#print axioms AlgebraicGeometry.exists_zeroSchemes_isFiniteLocallyFree_of_isLimit_finite
