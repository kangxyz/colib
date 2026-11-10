/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Simplex.SheafifiedChains
import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Actual Nisnevich consumers of ordinary algebraic singular chains

The tests use ordinary abelian-group presheaves on the existing smooth site.
They check the literal relative-product term, the two ordered face signs, the
actual sheafification unit and the natural homology comparison. No transfer
functor or replacement generic complex is assumed.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicTopology
open AlgebraicGeometry.Scheme AlgebraicSimplex
open scoped Simplicial

universe u

noncomputable section

variable (R : Type u) [CommRing R]
variable (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

example (n : ℕ) (U : SmoothSite (Spec (.of R))) :
    (((singularChainsFunctor R).obj P).X n).obj (op U) =
      P.obj (op (SmoothSite.product U (smoothSiteObj R n))) := rfl

example (n : ℕ) :
    ((singularChainsSheafificationUnit R
      (SmoothSite.nisnevichTopology (Spec (.of R)))).app P).f n =
      toSheafify (SmoothSite.nisnevichTopology (Spec (.of R)))
        (((singularChainsFunctor R).obj P).X n) := rfl

example :
    ((sheafifiedSingularChainsFunctor R
      (SmoothSite.nisnevichTopology (Spec (.of R)))).obj P).d 1 0 =
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of R)))
        AddCommGrpCat.{u + 1}).map ((simplicialPresheaf R P).δ (0 : Fin 2)) -
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of R)))
        AddCommGrpCat.{u + 1}).map ((simplicialPresheaf R P).δ (1 : Fin 2)) := by
  rw [sheafifiedSingularChainsFunctor_obj_d]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

example (n : ℕ) :
    ((sheafifiedSingularChainsFunctor R
      (SmoothSite.nisnevichTopology (Spec (.of R)))).obj P).homology n ≅
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of R)))
        AddCommGrpCat.{u + 1}).obj (((singularChainsFunctor R).obj P).homology n) :=
  sheafifiedSingularChainsHomologyIso R _ P n

example {Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (α : P ⟶ Q) (n : ℕ) :
    HomologicalComplex.homologyMap ((sheafifiedSingularChainsFunctor R
      (SmoothSite.nisnevichTopology (Spec (.of R)))).map α) n ≫
      (sheafifiedSingularChainsHomologyIso R _ Q n).hom =
    (sheafifiedSingularChainsHomologyIso R _ P n).hom ≫
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of R)))
        AddCommGrpCat.{u + 1}).map
          (HomologicalComplex.homologyMap ((singularChainsFunctor R).map α) n) :=
  sheafifiedSingularChainsHomologyIso_hom_naturality R _ α n
