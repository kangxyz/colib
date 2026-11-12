/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.FiniteSectionPairs

/-! # Actual finite section-family and whole-zero same-stage descent regression -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Morphisms
open Stacks.AlgebraicGeometry.ModuleLimits
universe u v w
example
    {I : Type u} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D C : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (C.map f)]
    [∀ i, IsNoetherian (D.obj i)] [∀ i, IsNoetherian (C.obj i)]
    (d : Cone D) (hd : IsLimit d) (c : Cone C) (hc : IsLimit c)
    (q : C ⟶ D) [∀ i, LocallyOfFiniteType (q.app i)] (qLimit : c.pt ⟶ d.pt)
    (hLimit : ∀ i, IsPullback (c.π.app i) qLimit (q.app i) (d.π.app i))
    (hcart : ∀ {i j} (f : j ⟶ i), IsPullback (C.map f) (q.app j) (q.app i) (D.map f))
    (i : I) {κ : Type w} [Finite κ] (L : κ → (C.obj i).Modules)
    [∀ a, (L a).IsFinitePresentation]
    [∀ a, SheafOfModules.IsInvertible
      (C.obj i).sheaf.obj (C.obj i).ringCatSheaf.property (L a)]
    (s : ∀ a, Γ((Scheme.Modules.pullback (c.π.app i)).obj (L a), ⊤))
    (hs : ∀ a, IsFiniteLocallyFree
      ((zeroScheme c.pt ((Scheme.Modules.pullback (c.π.app i)).obj (L a)) (s a)).subschemeι ≫
        qLimit)) :
    ∃ (j : I) (e : j ⟶ i)
      (t : ∀ a, Γ((Scheme.Modules.pullback (C.map e)).obj (L a), ⊤))
      (k : I) (f : k ⟶ j),
      (∀ a, Scheme.Modules.Hom.app
        (canHom (c.π.app j) (C.map e) (c.π.app i) (c.w e) (L a)) ⊤
        (pullbackGlobalSections (c.π.app j)
          ((Scheme.Modules.pullback (C.map e)).obj (L a)) (t a)) = s a) ∧
      ∀ a, IsFiniteLocallyFree
        ((zeroScheme (C.obj k)
          ((Scheme.Modules.pullback (C.map f)).obj
            ((Scheme.Modules.pullback (C.map e)).obj (L a)))
          (pullbackGlobalSections (C.map f)
            ((Scheme.Modules.pullback (C.map e)).obj (L a)) (t a))).subschemeι ≫ q.app k) ∧
        (zeroScheme (C.obj k)
          ((Scheme.Modules.pullback (C.map f)).obj
            ((Scheme.Modules.pullback (C.map e)).obj (L a)))
          (pullbackGlobalSections (C.map f)
            ((Scheme.Modules.pullback (C.map e)).obj (L a)) (t a))).comap (c.π.app k) =
          zeroScheme c.pt ((Scheme.Modules.pullback (c.π.app i)).obj (L a)) (s a) :=
  exists_sections_and_finiteLocallyFree_zeroSchemes_of_isLimit
    D C d hd c hc q qLimit hLimit hcart i L s hs

#print axioms AlgebraicGeometry.exists_sections_and_finiteLocallyFree_zeroSchemes_of_isLimit
