/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.FiniteMorphisms
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.FiniteZeroSchemes
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSections
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence

/-! # Canonical descent of actual global section values and their whole zero schemes

The native module-morphism descent is read through the original global-section
maps. The section values, canonical pullback isomorphisms and full zero schemes
are retained, rather than replacing them by a new unspecified section witness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules Stacks.Divisors

universe u v w

-- Use the same native sheaf/module interface aliases as FiniteMorphisms.
attribute [local implicit_reducible] TopCat.Sheaf Scheme.Modules
  Scheme.Modules.instCategory Scheme.unitModule

namespace Stacks.AlgebraicGeometry.ModuleLimits

private theorem unitHomEquivTop_app {X : Scheme.{u}} {M N : X.Modules}
    (θ : M ⟶ N) (x : Γ(M, ⊤)) :
    unitHomEquivTop N (Hom.app θ ⊤ x) = unitHomEquivTop M x ≫ θ := by
  apply (SheafOfModules.unitHomEquiv N).injective
  refine (unitHomEquiv_unitHomEquivTop N _).trans ?_
  refine Eq.trans ?_ (SheafOfModules.unitHomEquiv_comp_apply
    (unitHomEquivTop M x) θ).symm
  refine Eq.trans ?_ (congrArg (SheafOfModules.sectionsMap θ)
    (unitHomEquiv_unitHomEquivTop M x)).symm
  ext U
  simp only [sectionsTopEquiv_val, sectionsMap_val]
  exact (PresheafOfModules.naturality_apply θ.val (homOfLE (show U.unop ≤ ⊤ from le_top)).op x).symm

/-- The native geometric global-section pullback is the original pullback of its
morphism from the structure sheaf, with the canonical unit comparison. -/
theorem unitHomEquivTop_pullbackGlobalSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (x : Γ(M, ⊤)) :
    unitHomEquivTop ((Scheme.Modules.pullback f).obj M) (pullbackGlobalSections f M x) =
      (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map (unitHomEquivTop M x) := by
  have H := pullbackUnitIso_sections_naturality f M ((Scheme.Modules.pullback f).obj M) (𝟙 _) x
  rw [Adjunction.homEquiv_id, Category.comp_id] at H
  change (pullbackUnitIso f).hom ≫
    unitHomEquivTop ((Scheme.Modules.pullback f).obj M) (pullbackGlobalSections f M x) = _ at H
  apply (cancel_epi (pullbackUnitIso f).hom).mp
  rw [Iso.hom_inv_id_assoc]
  exact H

/-- Finitely many actual top-open section values descend to one stage and recover
exactly the original values through the specified canonical pullback comparison. -/
theorem exists_globalSections_pullback_canonical_of_isLimit_finite
    {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D) (hc : IsLimit c)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) {κ : Type w} [Finite κ] (L : κ → (D.obj i).Modules)
    [∀ a, (L a).IsFinitePresentation]
    (s : ∀ a, Γ((Scheme.Modules.pullback (c.π.app i)).obj (L a), ⊤)) :
    ∃ (j : I) (e : j ⟶ i)
      (t : ∀ a, Γ((Scheme.Modules.pullback (D.map e)).obj (L a), ⊤)), ∀ a,
      Hom.app (canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) (L a)) ⊤
        (pullbackGlobalSections (c.π.app j)
          ((Scheme.Modules.pullback (D.map e)).obj (L a)) (t a)) = s a := by
  let s' a := sectionsTopEquiv _ (s a)
  obtain ⟨j, e, t, ht⟩ := exists_sections_pullback_canonical_of_isLimit_finite D c hc i L s'
  refine ⟨j, e, fun a => (sectionsTopEquiv _).symm (t a), fun a => ?_⟩
  apply (unitHomEquivTop _).injective
  rw [unitHomEquivTop_app, unitHomEquivTop_pullbackGlobalSections, Category.assoc]
  change (pullbackUnitIso (c.π.app j)).inv ≫
    (Scheme.Modules.pullback (c.π.app j)).map
      ((SheafOfModules.unitHomEquiv _).symm
        (sectionsTopEquiv _ ((sectionsTopEquiv _).symm (t a)))) ≫
      canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) (L a) =
    (SheafOfModules.unitHomEquiv _).symm (sectionsTopEquiv _ (s a))
  simpa only [Equiv.apply_symm_apply] using ht a

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      Y.sheaf.obj Y.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

/-- Descent retains both the actual original section values and their full ideal
sheaves after the canonical comparison of iterated pullbacks. -/
theorem exists_globalSections_zeroSchemes_canonical_of_isLimit_finite
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
        _root_.AlgebraicGeometry.zeroScheme c.pt
          ((Scheme.Modules.pullback (c.π.app i)).obj (L a)) (s a) := by
  obtain ⟨j, e, t, ht⟩ :=
    exists_globalSections_pullback_canonical_of_isLimit_finite D c hc i L s
  exact ⟨j, e, t, fun a => ⟨ht a,
    _root_.AlgebraicGeometry.zeroScheme_eq_of_iso
      (canIso (c.π.app j) (D.map e) (c.π.app i) (c.w e) (L a)) (ht a)⟩⟩

end Stacks.AlgebraicGeometry.ModuleLimits
