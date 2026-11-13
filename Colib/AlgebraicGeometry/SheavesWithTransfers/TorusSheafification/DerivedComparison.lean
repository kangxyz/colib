/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.Complex
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# The natural derived comparison for torus sheafification

Both sides of the actual complex comparison factor through the original
localization of transfer presheaf complexes. Its lift retains the
termwise sheafification map followed by the genuine derived unit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe w w' u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The original torus parameter functor on the large transfer presheaves. -/
abbrev torusSectionsPresheafFunctor :
    PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k :=
  withParameterFunctor (SmoothSite.multiplicativeGroupObject (Spec (.of k)))

/-- The coefficient comparison defined by the original sheafification unit. -/
def torusSectionsSheafificationNatTrans :
    torusSectionsPresheafFunctor k ⋙ nisnevichSheafify k ⟶
      nisnevichSheafify k ⋙ torusSectionsFunctor k where
  app P := torusSectionsSheafificationComparison k P
  naturality _ _ f := torusSectionsSheafificationComparison_naturality k f

private def torusSectionsSheafificationCochainNatTrans :
    (torusSectionsPresheafFunctor k).mapHomologicalComplex (.up ℤ) ⋙
        (nisnevichSheafify k).mapHomologicalComplex (.up ℤ) ⟶
      (nisnevichSheafify k).mapHomologicalComplex (.up ℤ) ⋙
        (torusSectionsFunctor k).mapHomologicalComplex (.up ℤ) :=
  (torusSectionsSheafificationNatTrans k).mapHomologicalComplex (.up ℤ)

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

/-- The original comparison lifted through the actual derived localization. -/
@[no_expose]
def torusSectionsDerivedSheafificationComparison :
    (torusSectionsPresheafFunctor k).mapDerivedCategory ⋙
        (nisnevichSheafify k).mapDerivedCategory ⟶
      (nisnevichSheafify k).mapDerivedCategory ⋙ torusSectionsDerivedFunctor k := by
  let t := torusSectionsPresheafFunctor k
  let a := nisnevichSheafify k
  let R := torusSectionsDerivedFunctor k
  let q : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ ⥤
      DerivedCategory (PresheafWithTransfers.{u + 1} k) := DerivedCategory.Q
  let Q : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ ⥤
      DerivedCategory (SheafWithTransfers.{u + 1} k) := DerivedCategory.Q
  let W := HomologicalComplex.quasiIso (PresheafWithTransfers.{u + 1} k) (.up ℤ)
  let F₁ := t.mapHomologicalComplex (.up ℤ) ⋙ a.mapHomologicalComplex (.up ℤ) ⋙ Q
  let F₂ := a.mapHomologicalComplex (.up ℤ) ⋙ Q ⋙ R
  let G₁ := t.mapDerivedCategory ⋙ a.mapDerivedCategory
  let G₂ := a.mapDerivedCategory ⋙ R
  let e₁ : q ⋙ G₁ ≅ F₁ :=
    Functor.isoWhiskerRight t.mapDerivedCategoryFactors a.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (t.mapHomologicalComplex (.up ℤ)) a.mapDerivedCategoryFactors
  let e₂ : q ⋙ G₂ ≅ F₂ := Functor.isoWhiskerRight a.mapDerivedCategoryFactors R
  let : Localization.Lifting q W F₁ G₁ := ⟨e₁⟩
  let : Localization.Lifting q W F₂ G₂ := ⟨e₂⟩
  exact Localization.liftNatTrans q W F₁ F₂ G₁ G₂
    (Functor.whiskerRight (torusSectionsSheafificationCochainNatTrans k) Q ≫
      Functor.whiskerLeft (a.mapHomologicalComplex (.up ℤ)) (torusSectionsDerivedUnit k))

/-- On an original complex, the derived comparison has the prescribed
termwise map and the prescribed torus derived unit. -/
@[reassoc]
theorem torusSectionsDerivedSheafificationComparison_app_Q_obj
    (K : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ) :
    (torusSectionsDerivedSheafificationComparison k).app (DerivedCategory.Q.obj K) =
      (nisnevichSheafify k).mapDerivedCategory.map
          ((torusSectionsPresheafFunctor k).mapDerivedCategoryFactors.hom.app K) ≫
        (nisnevichSheafify k).mapDerivedCategoryFactors.hom.app
          (((torusSectionsPresheafFunctor k).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (torusSectionsSheafificationComplexMap k (.up ℤ) K) ≫
        (torusSectionsDerivedUnit k).app
          (((nisnevichSheafify k).mapHomologicalComplex (.up ℤ)).obj K) ≫
        (torusSectionsDerivedFunctor k).map
          ((nisnevichSheafify k).mapDerivedCategoryFactors.inv.app K) := by
  unfold torusSectionsDerivedSheafificationComparison
  rw [Localization.liftNatTrans_app]
  simp only [NatTrans.comp_app, Iso.trans_hom, Category.assoc]
  rfl

end AlgebraicGeometry.SheafWithTransfers
