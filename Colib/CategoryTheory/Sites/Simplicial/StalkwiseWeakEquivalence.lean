/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.PointedPresheaf
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Stalkwise weak equivalences of pointed simplicial presheaves

A site point takes the actual fiber of the underlying simplicial presheaf.
The stalkwise weak-equivalence class tests these fibers in the same
simplicial realization model as the objectwise class. The formal
localization inverts these maps. Identification with a local model
structure requires the site-specific comparison.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] {J : GrothendieckTopology C}

/-- The simplicial fiber at an actual point of the site. -/
def fiberAtPoint (Φ : J.Point.{w}) : PointedSimplicialPresheaf.{w} C ⥤ SSet.{w} :=
  forget C ⋙ Φ.presheafFiber

/-- Maps inducing a realization weak equivalence at every point of the site. -/
def stalkwiseWeakEquivalences (J : GrothendieckTopology C) :
    MorphismProperty (PointedSimplicialPresheaf.{w} C) :=
  fun _ _ f ↦ ∀ Φ : J.Point.{w}, SSet.realizationWeakEquivalences ((fiberAtPoint C Φ).map f)

theorem stalkwiseWeakEquivalences_iff {F G : PointedSimplicialPresheaf.{w} C} (f : F ⟶ G) :
    stalkwiseWeakEquivalences C J f ↔
      ∀ Φ : J.Point.{w}, SSet.IsRealizationWeakEquivalence ((fiberAtPoint C Φ).map f) :=
  Iff.rfl

instance : (stalkwiseWeakEquivalences.{w} C J).IsMultiplicative where
  id_mem F Φ := by
    rw [Functor.map_id]
    exact SSet.realizationWeakEquivalences.id_mem _
  comp_mem f g hf hg Φ := by
    rw [Functor.map_comp]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ (hf Φ) (hg Φ)

instance : (stalkwiseWeakEquivalences.{w} C J).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg Φ := by
    have h := hfg Φ
    rw [Functor.map_comp] at h
    exact SSet.realizationWeakEquivalences.of_postcomp _ _ (hg Φ) h
  of_precomp f g hf hfg Φ := by
    have h := hfg Φ
    rw [Functor.map_comp] at h
    exact SSet.realizationWeakEquivalences.of_precomp _ _ (hf Φ) h

/-- The formal localization at the stalkwise weak equivalences of the site. -/
abbrev StalkwiseHomotopyCategory (J : GrothendieckTopology C) :=
  (stalkwiseWeakEquivalences.{w} C J).Localization

/-- The canonical functor inverting the stalkwise weak equivalences. -/
abbrev toStalkwiseHomotopyCategory (J : GrothendieckTopology C) :
    PointedSimplicialPresheaf.{w} C ⥤ StalkwiseHomotopyCategory.{w} C J :=
  (stalkwiseWeakEquivalences C J).Q

theorem isIso_toStalkwiseHomotopyCategory_map {F G : PointedSimplicialPresheaf.{w} C}
    (f : F ⟶ G) (hf : stalkwiseWeakEquivalences C J f) :
    IsIso ((toStalkwiseHomotopyCategory C J).map f) :=
  (stalkwiseWeakEquivalences C J).Q_inverts f hf

end CategoryTheory.PointedSimplicialPresheaf
