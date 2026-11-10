/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Simplex.OrdinaryCochains
import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Actual cochain placement and sheafification consumers

For ordinary abelian-group presheaves on the smooth Nisnevich site, degree one
at weight two is the original singular chain-one term. The differential to
degree two is exactly sheafified face zero minus face one. The all-degree
homology comparison and vanishing above the bound use the native objects.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicTopology
open AlgebraicGeometry.Scheme AlgebraicSimplex
open scoped Simplicial

universe u

noncomputable section

variable (R : Type u) [CommRing R]
variable (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

example (q : ℕ) :
    (((sheafifiedSingularChainsFunctor R
      (SmoothSite.nisnevichTopology (Spec (.of R)))).obj P).extend
        (ComplexShape.embeddingUpIntLE (q : ℤ))) ≅
      (sheafifiedSingularCochainsFunctor R
        (SmoothSite.nisnevichTopology (Spec (.of R))) q).obj P :=
  sheafifiedSingularCochainsExtendIso R _ P q

example :
    ((sheafifiedSingularCochainsFunctor R
      (SmoothSite.nisnevichTopology (Spec (.of R))) 2).obj P).X 1 ≅
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of R)))
        AddCommGrpCat.{u + 1}).obj ((simplicialPresheaf R P).obj (op ⦋1⦌)) :=
  sheafifiedSingularCochainsXIso R _ P 2 1

example (q : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero (((sheafifiedSingularCochainsFunctor R
      (SmoothSite.nisnevichTopology (Spec (.of R))) q).obj P).X i) :=
  isZero_sheafifiedSingularCochainsFunctor_obj_X R _ P q i hi

example :
    ((sheafifiedSingularCochainsFunctor R
      (SmoothSite.nisnevichTopology (Spec (.of R))) 2).obj P).d 1 2 =
      (sheafifiedSingularCochainsXIso R _ P 2 1).hom ≫
        ((presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of R)))
          AddCommGrpCat.{u + 1}).map ((simplicialPresheaf R P).δ (0 : Fin 2)) -
         (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of R)))
          AddCommGrpCat.{u + 1}).map ((simplicialPresheaf R P).δ (1 : Fin 2))) ≫
        (sheafifiedSingularCochainsXIso R _ P 2 0).inv := by
  have h : ((sheafifiedSingularChainsFunctor R
      (SmoothSite.nisnevichTopology (Spec (.of R)))).obj P).d 1 0 =
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of R)))
        AddCommGrpCat.{u + 1}).map ((simplicialPresheaf R P).δ (0 : Fin 2)) -
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of R)))
        AddCommGrpCat.{u + 1}).map ((simplicialPresheaf R P).δ (1 : Fin 2)) := by
    rw [sheafifiedSingularChainsFunctor_obj_d]
    simp [Fin.sum_univ_two, sub_eq_add_neg]
  exact (sheafifiedSingularCochainsFunctor_obj_d R
    (SmoothSite.nisnevichTopology (Spec (.of R))) P 2 1 0).trans
      (congrArg (fun f => (sheafifiedSingularCochainsXIso R _ P 2 1).hom ≫ f ≫
        (sheafifiedSingularCochainsXIso R _ P 2 0).inv) h)

example (q r : ℕ) :
    ((sheafifiedSingularCochainsFunctor R
      (SmoothSite.nisnevichTopology (Spec (.of R))) q).obj P).homology ((q : ℤ) - r) ≅
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of R)))
        AddCommGrpCat.{u + 1}).obj (((singularChainsFunctor R).obj P).homology r) :=
  sheafifiedSingularCochainsHomologyIso R _ P q r
