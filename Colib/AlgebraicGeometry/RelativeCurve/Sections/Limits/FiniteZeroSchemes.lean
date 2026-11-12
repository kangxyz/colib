/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction

/-! # Actual finite locally free zero schemes descend from a scheme limit

The section and its invertible module are fixed at a stage. The hypotheses concern
the whole zero scheme of their literal pullback to the limit. Native zero-scheme
base change and native finite-locally-free descent produce the same property at a
later stage. No reduced support or continuity certificate replaces the zero scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow Stacks.Divisors
open Stacks.Morphisms

universe u v w

namespace AlgebraicGeometry

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

/-- The native whole zero-scheme base-change isomorphism preserves the literal
structure map to the new base, hence finite local freeness. -/
theorem zeroSchemeBaseChange_finiteLocallyFree_iff {S T X : Scheme.{u}}
    (b : T ⟶ S) (q : X ⟶ S) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : Γ(L, ⊤)) :
    IsFiniteLocallyFree
      ((zeroScheme (pullback b q) ((Scheme.Modules.pullback (pullback.snd b q)).obj L)
        (pullbackGlobalSections (pullback.snd b q) L s)).subschemeι ≫ pullback.fst b q) ↔
      IsFiniteLocallyFree (pullback.fst b ((zeroScheme X L s).subschemeι ≫ q)) := by
  let e := zeroSchemeBaseChangeIso b q L s
  have he : e.hom ≫
      ((zeroScheme (pullback b q) ((Scheme.Modules.pullback (pullback.snd b q)).obj L)
        (pullbackGlobalSections (pullback.snd b q) L s)).subschemeι ≫ pullback.fst b q) =
      pullback.fst b ((zeroScheme X L s).subschemeι ≫ q) := by
    rw [← Category.assoc, zeroSchemeBaseChangeIso_hom_subschemeι]
    simp [bivariantBaseChangeMap]
  have H := MorphismProperty.cancel_left_of_respectsIso
    (P := @IsFiniteLocallyFree) e.hom
    ((zeroScheme (pullback b q) ((Scheme.Modules.pullback (pullback.snd b q)).obj L)
      (pullbackGlobalSections (pullback.snd b q) L s)).subschemeι ≫ pullback.fst b q)
  rw [he] at H
  exact H.symm

private theorem finiteLocallyFree_overPullback_terminal_iff {S T : Scheme.{u}}
    (b : T ⟶ S) (Z : Over S) :
    IsFiniteLocallyFree ((Over.pullback b).map
      (Over.homMk Z.hom (by exact Category.comp_id _) : Z ⟶ Over.mk (𝟙 S))).left ↔
      IsFiniteLocallyFree (pullback.fst b Z.hom) := by
  rw [← baseChangeMap_prop_iff (@IsFiniteLocallyFree) b Z (Over.mk (𝟙 S))
    (Over.homMk Z.hom (by exact Category.comp_id _))]
  rw [← MorphismProperty.cancel_right_of_respectsIso (P := @IsFiniteLocallyFree)
    (baseChangeMap b Z (Over.mk (𝟙 S)) (Over.homMk Z.hom (by exact Category.comp_id _)))
    (pullback.fst b (𝟙 S))]
  exact (congrArg (@IsFiniteLocallyFree _ _)
    (baseChangeMap_fst b Z (Over.mk (𝟙 S))
      (Over.homMk Z.hom (by exact Category.comp_id _)))).to_iff

/-- Finite local freeness of the actual limit zero scheme is realized at a later
stage for the original section. This uses the native finite-presentation descent
of the entire morphism, not flatness of any integral support component. -/
@[stacks 06AC "whole zero schemes of the original pulled-back invertible section"]
theorem exists_zeroScheme_isFiniteLocallyFree_of_isLimit
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : I) [IsNoetherian (D.obj i)]
    {X : Scheme.{u}} [IsNoetherian X] (q : X ⟶ D.obj i) [LocallyOfFiniteType q]
    (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (h : IsFiniteLocallyFree
      ((zeroScheme (pullback (c.π.app i) q)
        ((Scheme.Modules.pullback (pullback.snd (c.π.app i) q)).obj L)
        (pullbackGlobalSections (pullback.snd (c.π.app i) q) L s)).subschemeι ≫
          pullback.fst (c.π.app i) q)) :
    ∃ (j : I) (f : j ⟶ i), IsFiniteLocallyFree
      ((zeroScheme (pullback (D.map f) q)
        ((Scheme.Modules.pullback (pullback.snd (D.map f) q)).obj L)
        (pullbackGlobalSections (pullback.snd (D.map f) q) L s)).subschemeι ≫
          pullback.fst (D.map f) q) := by
  let Z : Over (D.obj i) := Over.mk ((zeroScheme X L s).subschemeι ≫ q)
  let Y : Over (D.obj i) := Over.mk (𝟙 (D.obj i))
  let g : Z ⟶ Y := Over.homMk Z.hom (by exact Category.comp_id _)
  let : IsNoetherian Z.left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (Y := X) (zeroScheme X L s).subschemeι
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
        (Y := X) (zeroScheme X L s).subschemeι }
  let : IsNoetherian Y.left := ‹IsNoetherian (D.obj i)›
  let : LocallyOfFiniteType g.left :=
    inferInstanceAs (LocallyOfFiniteType ((zeroScheme X L s).subschemeι ≫ q))
  have : IsFiniteLocallyFree ((Over.pullback (c.π.app i)).map g).left :=
    (finiteLocallyFree_overPullback_terminal_iff (c.π.app i) Z).mpr
      ((zeroSchemeBaseChange_finiteLocallyFree_iff (c.π.app i) q L s).mp h)
  obtain ⟨j, f, hf⟩ := exists_isFiniteLocallyFree_baseChange_of_isLimit D c hc i Z Y g
  exact ⟨j, f, (zeroSchemeBaseChange_finiteLocallyFree_iff (D.map f) q L s).mpr
    ((finiteLocallyFree_overPullback_terminal_iff (D.map f) Z).mp hf)⟩

/-- Finitely many original zero schemes become finite locally free at one common
stage. In particular the actual numerator and denominator use the same transition. -/
@[stacks 06AC "simultaneous finite family of whole zero schemes of original sections",
  colib_tag "COL-1110"]
theorem exists_zeroSchemes_isFiniteLocallyFree_of_isLimit_finite
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
  let Z (a : κ) : Over (D.obj i) := Over.mk ((zeroScheme X (L a) (s a)).subschemeι ≫ q)
  let Y (_ : κ) : Over (D.obj i) := Over.mk (𝟙 (D.obj i))
  let g (a : κ) : Z a ⟶ Y a := Over.homMk (Z a).hom (by exact Category.comp_id _)
  have H (a : κ) : ∃ (j : I) (f : j ⟶ i),
      IsFiniteLocallyFree ((Over.pullback (D.map f)).map (g a)).left := by
    obtain ⟨j, f, hf⟩ := exists_zeroScheme_isFiniteLocallyFree_of_isLimit
      D c hc i q (L a) (s a) (h a)
    exact ⟨j, f, (finiteLocallyFree_overPullback_terminal_iff (D.map f) (Z a)).mpr
      ((zeroSchemeBaseChange_finiteLocallyFree_iff (D.map f) q (L a) (s a)).mp hf)⟩
  obtain ⟨j, f, hf⟩ := common_stage_of_finite_prop (@IsFiniteLocallyFree) D i Z Y g H
  exact ⟨j, f, fun a =>
    (zeroSchemeBaseChange_finiteLocallyFree_iff (D.map f) q (L a) (s a)).mpr
      ((finiteLocallyFree_overPullback_terminal_iff (D.map f) (Z a)).mp (hf a))⟩

end AlgebraicGeometry
