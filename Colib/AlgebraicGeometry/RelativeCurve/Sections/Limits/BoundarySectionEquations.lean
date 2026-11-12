/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.AuxiliaryPairFrames
public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryFrames
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer.GlobalSections

/-! # Original boundary section values and normalized finite linear equations

The full scheme square and its canonical module comparison identify the actual
boundary value one with the normalized morphism equation used by native frame
descent. Neither that equation nor the matching of the sections is assumed.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
namespace AlgebraicGeometry.Scheme.Modules

attribute [local implicit_reducible] TopCat.Sheaf Scheme.Modules
  Scheme.Modules.instCategory Scheme.unitModule

private theorem cancel_iso_linear {C : Type*} [Category C] {U V A B : C}
    (u : U ≅ V) (v : A ≅ B) (f g : V ⟶ A) :
    f = g ↔ u.hom ≫ f ≫ v.hom = u.hom ≫ g ≫ v.hom := by
  simp only [← Category.assoc, cancel_mono, cancel_epi]

/-- Normalized pullback of the original unit-valued section is still the map
attached to the actual value one. -/
theorem pullback_unitHomEquivTop_one {A B : Scheme.{u}} (f : A ⟶ B) :
    (pullbackUnitIso f).inv ≫
      (pullback f).map (unitHomEquivTop (SheafOfModules.unit B.ringCatSheaf)
        (1 : Γ(B, ⊤))) ≫ (pullbackUnitIso f).hom =
      unitHomEquivTop (SheafOfModules.unit A.ringCatSheaf) (1 : Γ(A, ⊤)) := by
  have H := unitHomEquivTop_pullbackGlobalSections f
    (SheafOfModules.unit B.ringCatSheaf) (1 : Γ(B, ⊤))
  have H' : unitHomEquivTop _
      (pullbackGlobalSections f (SheafOfModules.unit B.ringCatSheaf) (1 : Γ(B, ⊤))) ≫
        (pullbackUnitIso f).hom =
      unitHomEquivTop (SheafOfModules.unit A.ringCatSheaf) (1 : Γ(A, ⊤)) :=
    (unitHomEquivTop_comp_eq_iff _ _ _).mpr
      ((SectionsEqualizer.pullbackUnitIso_unit f (1 : Γ(B, ⊤))).trans (map_one f.appTop.hom))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ (pullbackUnitIso f).hom) H.symm).trans H')

private theorem normalize_composite {C : Type*} [Category C] {U V P Q R : C}
    (u : U ⟶ V) (a : V ⟶ P) (n : P ⟶ Q) (v : Q ⟶ R)
    (t : U ⟶ P) (e : P ⟶ R) (hs : u ≫ a = t) (hn : n ≫ v = e) :
    u ≫ (a ≫ n) ≫ v = t ≫ e := by
  calc
    _ = (u ≫ a) ≫ (n ≫ v) := by simp only [Category.assoc]
    _ = _ := congrArg₂ (fun x y => x ≫ y) hs hn

/-- The actual boundary section, transported through the original square,
is normalized to one exactly when the original finite linear equation holds. -/
theorem framePullbackIso_section_one_iff {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D)
    (w : f ≫ g = h ≫ k) (M : D.Modules)
    (e : (pullback h).obj ((pullback k).obj M) ≅ SheafOfModules.unit A.ringCatSheaf)
    (s : Γ((pullback g).obj M, ⊤)) :
    (pullback f).map (unitHomEquivTop ((pullback g).obj M) s) ≫
        (framePullbackIso f g h k w M e).hom =
      (pullback f).map (unitHomEquivTop (SheafOfModules.unit B.ringCatSheaf)
        (1 : Γ(B, ⊤))) ↔
    Hom.app (pullbackSquareIso f g h k w M ≪≫ e).hom ⊤
      (pullbackGlobalSections f ((pullback g).obj M) s) = (1 : Γ(A, ⊤)) := by
  have he : (framePullbackIso f g h k w M e).hom ≫ (pullbackUnitIso f).hom =
      (pullbackSquareIso f g h k w M ≪≫ e).hom := by
    simp only [framePullbackIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hs := (unitHomEquivTop_pullbackGlobalSections f ((pullback g).obj M) s).symm
  have hl := normalize_composite (pullbackUnitIso f).inv _
    (framePullbackIso f g h k w M e).hom (pullbackUnitIso f).hom _ _ hs he
  exact (cancel_iso_linear (pullbackUnitIso f).symm (pullbackUnitIso f) _ _).trans
    ((Iff.of_eq (congrArg₂ (fun a b => a = b) hl (pullback_unitHomEquivTop_one f))).trans
      (unitHomEquivTop_comp_eq_iff _ _ _))

/-- The specified canonical comparison carries the actual iterated global-section
pullback to the original composite pullback, including its prescribed map equality. -/
theorem canIso_pullbackGlobalSections {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (p : W ⟶ Y) (hp : f ≫ g = p) (M : Y.Modules) (s : Γ(M, ⊤)) :
    Hom.app (canIso f g p hp M).hom ⊤
      (pullbackGlobalSections f ((pullback g).obj M) (pullbackGlobalSections g M s)) =
      pullbackGlobalSections p M s := by
  change Hom.app ((pullbackCongr hp).app M).hom ⊤
    (Hom.app ((pullbackComp f g).app M).hom ⊤
      (pullbackGlobalSections f ((pullback g).obj M) (pullbackGlobalSections g M s))) = _
  exact (congrArg (Hom.app ((pullbackCongr hp).app M).hom ⊤)
    (SectionsEqualizer.pullbackGlobalSections_comp f g M s)).trans
      (SectionsEqualizer.pullbackGlobalSections_congr hp M s)

/-- The original square comparison carries the two actual paths of global-section
pullback to one another. There is no supplied compatibility certificate. -/
theorem pullbackSquareIso_pullbackGlobalSections {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D)
    (w : f ≫ g = h ≫ k) (M : D.Modules) (s : Γ(M, ⊤)) :
    Hom.app (pullbackSquareIso f g h k w M).hom ⊤
      (pullbackGlobalSections f ((pullback g).obj M) (pullbackGlobalSections g M s)) =
      pullbackGlobalSections h ((pullback k).obj M) (pullbackGlobalSections k M s) := by
  change Hom.app (canIso h k (h ≫ k) rfl M).inv ⊤
    (Hom.app (canIso f g (h ≫ k) w M).hom ⊤
      (pullbackGlobalSections f ((pullback g).obj M) (pullbackGlobalSections g M s))) = _
  exact (congrArg (Hom.app (canIso h k (h ≫ k) rfl M).inv ⊤)
    (canIso_pullbackGlobalSections f g (h ≫ k) w M s)).trans
      ((congrArg (Hom.app (canIso h k (h ≫ k) rfl M).inv ⊤)
        (canIso_pullbackGlobalSections h k (h ≫ k) rfl M s)).symm.trans
          (app_inv_app (canIso h k (h ≫ k) rfl M) ⊤ _))

/-- For an original ambient section, the actual full-boundary value one is
exactly the finite linear equation for the normalized frame. -/
theorem framePullbackIso_originalSection_one_iff {A B C D : Scheme.{u}}
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
        (1 : Γ(A, ⊤)) := by
  refine (framePullbackIso_section_one_iff f g h k w M e (pullbackGlobalSections g M s)).trans ?_
  have H := congrArg (Hom.app e.hom ⊤)
    (pullbackSquareIso_pullbackGlobalSections f g h k w M s)
  exact Iff.of_eq (congrArg (fun z => z = (1 : Γ(A, ⊤))) H)

end AlgebraicGeometry.Scheme.Modules
