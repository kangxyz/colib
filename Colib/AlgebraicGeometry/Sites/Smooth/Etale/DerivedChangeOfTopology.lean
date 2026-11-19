/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.ChangeOfTopology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Exact derived change from Nisnevich to étale sheaves

Exact étale sheafification induces a functor on the genuine unbounded derived
categories. The two sheafifications have canonically compatible free representing
sources, by uniqueness of left adjoints. Applying this exact functor and its
native shift and single-complex comparisons gives an additive map on actual
derived-Hom groups. No ordinary right adjoint is treated as a derived functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Stacks.Cohomology.FreeYonedaUnivLE

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (S : Scheme.{u})
variable [HasSheafify (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1}]
variable [HasSheafify (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1}]

/-- Successive Nisnevich and étale sheafification is canonically étale sheafification. -/
def nisnevichToEtaleSheafificationIso :
    presheafToSheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1} ⋙
    SmoothSite.nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1} ≅
    presheafToSheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1} :=
  Adjunction.leftAdjointUniq
    ((sheafificationAdjunction (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1}).comp
      (SmoothSite.nisnevichToEtaleSheafAdjunction S AddCommGrpCat.{u + 1}))
    (sheafificationAdjunction (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1})

/-- Exact change of topology takes the lifted free representing sheaf to its étale version. -/
def nisnevichToEtaleFreeYonedaIso : freeYoneda.{u + 1} (SmoothSite.nisnevichTopology S) ⋙
    SmoothSite.nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1} ≅
    freeYoneda.{u + 1} (SmoothSite.etaleTopology S) :=
  Functor.isoWhiskerLeft
    (uliftYoneda.{u + 1} ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free)
    (nisnevichToEtaleSheafificationIso S)

universe w w'
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w'}
  (Sheaf (SmoothSite.etaleTopology S) AddCommGrpCat.{u + 1})]

/-- The exact derived change-of-topology map on actual free-source hypercohomology. -/
@[colib_tag "COL-1228"]
def nisnevichToEtaleDerivedHomMap (X : SmoothSite S)
    (K : CochainComplex (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1}) ℤ)
    (p : ℤ) :
    (((DerivedCategory.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} (SmoothSite.nisnevichTopology S)).obj X)) ⟶
       (DerivedCategory.Q.obj K)⟦p⟧) →+
    (((DerivedCategory.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} (SmoothSite.etaleTopology S)).obj X)) ⟶
       (DerivedCategory.Q.obj
         (((SmoothSite.nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapHomologicalComplex
           (.up ℤ)).obj K))⟦p⟧) where
  toFun f :=
    (DerivedCategory.singleFunctor _ 0).map ((nisnevichToEtaleFreeYonedaIso S).inv.app X) ≫
    ((SmoothSite.nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapDerivedCategorySingleFunctor
      0).inv.app _ ≫
    (SmoothSite.nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapDerivedCategory.map f ≫
    ((SmoothSite.nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapDerivedCategory.commShiftIso
      p).hom.app (DerivedCategory.Q.obj K) ≫
    ((SmoothSite.nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapDerivedCategoryFactors.hom.app
      K)⟦p⟧'
  map_zero' := by simp
  map_add' f g := by simp [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

end AlgebraicGeometry.Scheme.SmoothSite
