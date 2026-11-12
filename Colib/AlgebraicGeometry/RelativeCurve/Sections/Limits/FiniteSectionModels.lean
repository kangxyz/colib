/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.FiniteSectionPairs

/-! # Original section models retain full zero schemes under simultaneous descent

The original sections are transported through specified actual module isomorphisms.
Native zero-scheme invariance then supplies the finite-local-freeness hypotheses
for common-stage section descent. The final full ideal remains the original one.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Stacks.Morphisms
open Stacks.AlgebraicGeometry.ModuleLimits
universe u v w
namespace AlgebraicGeometry
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

/-- Simultaneous descent starts from the original sections and original whole
zero schemes, preserving the specified actual module-model isomorphisms. -/
theorem exists_originalSections_finiteLocallyFree_zeroSchemes_of_isLimit
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
    (M : κ → c.pt.Modules)
    [∀ a, SheafOfModules.IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property (M a)]
    (E : ∀ a, M a ≅ (Scheme.Modules.pullback (c.π.app i)).obj (L a))
    (s : ∀ a, Γ(M a, ⊤))
    (hs : ∀ a, IsFiniteLocallyFree
      ((zeroScheme c.pt (M a) (s a)).subschemeι ≫
        qLimit)) :
    ∃ (j : I) (e : j ⟶ i)
      (t : ∀ a, Γ((Scheme.Modules.pullback (C.map e)).obj (L a), ⊤))
      (k : I) (f : k ⟶ j),
      (∀ a, Scheme.Modules.Hom.app
        (canHom (c.π.app j) (C.map e) (c.π.app i) (c.w e) (L a)) ⊤
        (pullbackGlobalSections (c.π.app j)
          ((Scheme.Modules.pullback (C.map e)).obj (L a)) (t a)) =
          Scheme.Modules.Hom.app (E a).hom ⊤ (s a)) ∧
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
          zeroScheme c.pt (M a) (s a) := by
  let s' a := Scheme.Modules.Hom.app (E a).hom ⊤ (s a)
  have hzero a : zeroScheme c.pt (M a) (s a) =
      zeroScheme c.pt ((Scheme.Modules.pullback (c.π.app i)).obj (L a)) (s' a) :=
    zeroScheme_eq_of_iso (E a) rfl
  have hs' a : IsFiniteLocallyFree
      ((zeroScheme c.pt ((Scheme.Modules.pullback (c.π.app i)).obj (L a)) (s' a)).subschemeι ≫
        qLimit) := by
    rw [← hzero a]
    exact hs a
  obtain ⟨j, e, t, k, f, ht, hz⟩ :=
    exists_sections_and_finiteLocallyFree_zeroSchemes_of_isLimit
      D C d hd c hc q qLimit hLimit hcart i L s' hs'
  exact ⟨j, e, t, k, f, ht, fun a => ⟨(hz a).1, (hz a).2.trans (hzero a).symm⟩⟩

end AlgebraicGeometry
