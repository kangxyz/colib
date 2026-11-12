/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.ModeledZeroSchemeRefinement

/-! # Refine the same sections and preserve their original whole zero ideals -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Morphisms
open Stacks.AlgebraicGeometry.ModuleLimits
universe u v w
namespace AlgebraicGeometry

example
    {I : Type u} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D C : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, IsNoetherian (D.obj i)] [∀ i, IsNoetherian (C.obj i)]
    (d : Cone D) (hd : IsLimit d) (c : Cone C)
    (q : C ⟶ D) [∀ i, LocallyOfFiniteType (q.app i)] (qLimit : c.pt ⟶ d.pt)
    (hLimit : ∀ i, IsPullback (c.π.app i) qLimit (q.app i) (d.π.app i))
    (hcart : ∀ {i j} (f : j ⟶ i), IsPullback (C.map f) (q.app j) (q.app i) (D.map f))
    (i : I) {κ : Type w} [Finite κ] (L : κ → (C.obj i).Modules)
    [∀ a, SheafOfModules.IsInvertible
      (C.obj i).sheaf.obj (C.obj i).ringCatSheaf.property (L a)]
    (M : κ → c.pt.Modules)
    [∀ a, SheafOfModules.IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property (M a)]
    (E : ∀ a, M a ≅ (Scheme.Modules.pullback (c.π.app i)).obj (L a))
    (s : ∀ a, Γ(M a, ⊤)) (t : ∀ a, Γ(L a, ⊤))
    (ht : ∀ a, Scheme.Modules.Hom.app (E a).hom ⊤ (s a) =
      pullbackGlobalSections (c.π.app i) (L a) (t a))
    (hs : ∀ a, IsFiniteLocallyFree ((zeroScheme c.pt (M a) (s a)).subschemeι ≫ qLimit)) :
    ∃ (j : I) (f : j ⟶ i), ∀ a,
      IsFiniteLocallyFree
        ((zeroScheme (C.obj j) ((Scheme.Modules.pullback (C.map f)).obj (L a))
          (pullbackGlobalSections (C.map f) (L a) (t a))).subschemeι ≫ q.app j) ∧
      (zeroScheme (C.obj j) ((Scheme.Modules.pullback (C.map f)).obj (L a))
        (pullbackGlobalSections (C.map f) (L a) (t a))).comap (c.π.app j) =
          zeroScheme c.pt (M a) (s a) :=
  exists_modeledZeroSchemes_finiteLocallyFree_refinement D C d hd c q qLimit hLimit hcart i L M E s t ht hs

#print axioms exists_modeledZeroSchemes_finiteLocallyFree_refinement

end AlgebraicGeometry
