/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Čech simplicial presheaves of smooth-scheme maps

The Čech nerve is Mathlib's augmented Čech nerve of the lifted Yoneda map.
Flipping its two variables yields a simplicial presheaf. A section supplies
Mathlib's extra degeneracy and simplicial contraction of the augmented nerve.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (S : Scheme.{u}) {X Y : SmoothSite S} (f : X ⟶ Y)

/-- The map of lifted representables induced by the smooth-site map. -/
def cechRepresentableMap :
    (uliftYoneda.{u + 1}).obj X ⟶ (uliftYoneda.{u + 1}).obj Y :=
  (uliftYoneda.{u + 1}).map f

/-- The augmented Čech nerve in presheaves of sets. -/
def augmentedCechPresheaf := (Arrow.mk (cechRepresentableMap S f)).augmentedCechNerve

/-- The simplicial presheaf obtained by flipping the native Čech nerve. -/
def cechSimplicialPresheaf : (SmoothSite S)ᵒᵖ ⥤ SSet.{u + 1} :=
  (augmentedCechPresheaf S f).left.flip

/-- The discrete simplicial presheaf represented by the target. -/
def cechBasePresheaf (Y : SmoothSite S) : (SmoothSite S)ᵒᵖ ⥤ SSet.{u + 1} :=
  ((Functor.const SimplexCategoryᵒᵖ).obj ((uliftYoneda.{u + 1}).obj Y)).flip

/-- The augmentation is the flipped native augmented Čech nerve map. -/
def cechAugmentation : cechSimplicialPresheaf S f ⟶ cechBasePresheaf S Y :=
  (CategoryTheory.flipFunctor _ _ _).map (augmentedCechPresheaf S f).hom

/-- A section induces the native extra degeneracy of the augmented Čech nerve. -/
def cechExtraDegeneracy (s : SplitEpi f) :
    SimplicialObject.Augmented.ExtraDegeneracy (augmentedCechPresheaf S f) :=
  Arrow.AugmentedCechNerve.extraDegeneracy _ (s.map (uliftYoneda.{u + 1}))

/-- A section contracts the native augmented Čech nerve onto the base, as a
simplicial homotopy in the category of presheaves of sets. -/
def cechContraction (s : SplitEpi f) :
    SimplicialObject.Homotopy
      ((augmentedCechPresheaf S f).hom ≫ (cechExtraDegeneracy S f s).section_)
      (𝟙 (augmentedCechPresheaf S f).left) :=
  (cechExtraDegeneracy S f s).homotopy

/-- The section of this contraction is a strict right inverse to the augmentation. -/
theorem cechContraction_section (s : SplitEpi f) :
    (cechExtraDegeneracy S f s).section_ ≫ (augmentedCechPresheaf S f).hom = 𝟙 _ :=
  (cechExtraDegeneracy S f s).section_comp_hom

/-- The represented base is terminal in the smooth site. -/
def cechBaseIsTerminal : IsTerminal (SmoothSite.base S) :=
  IsTerminal.ofUniqueHom SmoothSite.Contraction.toBase fun X f ↦ by
    apply MorphismProperty.Over.Hom.ext
    have h := MorphismProperty.Over.w f
    change f.left ≫ 𝟙 S = X.hom at h
    exact (Category.comp_id _).symm.trans h

/-- The discrete simplicial presheaf represented by the base is the point. -/
def cechBaseIsoPoint :
    cechBasePresheaf S (SmoothSite.base S) ≅ ⊤_ ((SmoothSite S)ᵒᵖ ⥤ SSet.{u + 1}) := by
  let F : SmoothSite S ⥤ (SmoothSite S)ᵒᵖ ⥤ SSet.{u + 1} :=
    uliftYoneda.{u + 1} ⋙
      (Functor.whiskeringRight _ _ _).obj (Functor.const SimplexCategoryᵒᵖ)
  let : PreservesLimit (Functor.empty.{0} (SmoothSite S)) F := by
    dsimp [F, uliftYoneda]
    infer_instance
  exact ((cechBaseIsTerminal S).isTerminalObj F).uniqueUpToIso terminalIsTerminal

end AlgebraicGeometry.MotivicHomotopy
