/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.CanonicalSections

/-! # Canonical original section and whole zero-scheme descent regression -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules
open Stacks.AlgebraicGeometry.ModuleLimits
universe u v w

example
    {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D) (hc : IsLimit c)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) {κ : Type w} [Finite κ] (L : κ → (D.obj i).Modules)
    [∀ a, (L a).IsFinitePresentation]
    [∀ a, AlgebraicGeometry.SheafOfModules.IsInvertible
      (D.obj i).sheaf.obj (D.obj i).ringCatSheaf.property (L a)]
    (s : ∀ a, Γ((Scheme.Modules.pullback (c.π.app i)).obj (L a), ⊤)) :
    ∃ (j : I) (e : j ⟶ i)
      (t : ∀ a, Γ((Scheme.Modules.pullback (D.map e)).obj (L a), ⊤)), ∀ a,
      Hom.app (canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) (L a)) ⊤
        (pullbackGlobalSections (c.π.app j)
          ((Scheme.Modules.pullback (D.map e)).obj (L a)) (t a)) = s a ∧
      _root_.AlgebraicGeometry.zeroScheme c.pt
        ((Scheme.Modules.pullback (c.π.app j)).obj
          ((Scheme.Modules.pullback (D.map e)).obj (L a)))
        (pullbackGlobalSections (c.π.app j)
          ((Scheme.Modules.pullback (D.map e)).obj (L a)) (t a)) =
        _root_.AlgebraicGeometry.zeroScheme c.pt ((Scheme.Modules.pullback (c.π.app i)).obj (L a)) (s a) :=
  exists_globalSections_zeroSchemes_canonical_of_isLimit_finite D c hc i L s

#print axioms Stacks.AlgebraicGeometry.ModuleLimits.unitHomEquivTop_pullbackGlobalSections
#print axioms Stacks.AlgebraicGeometry.ModuleLimits.exists_globalSections_pullback_canonical_of_isLimit_finite
#print axioms Stacks.AlgebraicGeometry.ModuleLimits.exists_globalSections_zeroSchemes_canonical_of_isLimit_finite
