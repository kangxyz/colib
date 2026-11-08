/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.FieldEvaluation
import Colib.CategoryTheory.Sites.Hypercohomology.SheafComparison
import Colib.CategoryTheory.Sites.Hypercohomology.Shift

/-! # Native unbounded hypercohomology and actual base-field consumer checks -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.FreeYonedaUnivLE

universe w w' t v u

noncomputable section

section ArbitrarySite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasDerivedCategory.{w'} (Sheaf J AddCommGrpCat.{max v t})]

example (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ) (p : ℤ) (X : C) :
    (hypercohomologyPresheaf J K p).obj (op X) =
      AddCommGrpCat.of
        ((DerivedCategory.singleFunctor _ 0).obj ((freeYoneda.{t} J).obj X) ⟶
          (DerivedCategory.Q.obj K)⟦p⟧) :=
  hypercohomologyPresheaf_obj J K p X

example {K L : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ}
    (f : K ⟶ L) [QuasiIso f] (p : ℤ) :
    IsIso ((hypercohomologyPresheafFunctor J p).map f) := inferInstance

example (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ) (q p : ℤ)
    {X Y : C} (f : X ⟶ Y) (x : (hypercohomologyPresheaf J (K⟦q⟧) p).obj (op Y)) :
    hypercohomologyShiftAddEquiv J K q p X
        ((hypercohomologyPresheaf J (K⟦q⟧) p).map f.op x) =
      (hypercohomologyPresheaf J K (q + p)).map f.op
        (hypercohomologyShiftAddEquiv J K q p Y x) :=
  hypercohomologyShiftAddEquiv_restriction J K q p f x

example [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]
    {F G : Sheaf J AddCommGrpCat.{max v t}} (η : F ⟶ G) (n : ℕ) (X : C)
    (x : (hypercohomologyPresheaf J
      ((CochainComplex.singleFunctor _ 0).obj F) (n : ℤ)).obj (op X)) :
    singleHypercohomologyEquivCohomology J G n X
        (((hypercohomologyPresheafFunctor J (n : ℤ)).map
          ((CochainComplex.singleFunctor _ 0).map η)).app (op X) x) =
      ((cohomologyPresheafFunctor.{w, t} J n).map η).app (op X)
        (singleHypercohomologyEquivCohomology J F n X x) :=
  singleHypercohomologyEquivCohomology_coefficient J η n X x

end ArbitrarySite

section BaseField

open SmoothSite

variable (k : Type u) [Field k]

example (F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsIso ((toSheafify (nisnevichTopology (Spec (.of k))) F).app
      (op (base (Spec (.of k))))) :=
  isIso_toSheafify_app_base k F

example (S : ShortComplex (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}))
    (hS : S.Exact) :
    (S.map ((sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
      (op (base (Spec (.of k)))))).Exact :=
  exact_map_sheafSections_base k S hS

example : Projective ((freeYoneda.{u + 1} (nisnevichTopology (Spec (.of k)))).obj
    (base (Spec (.of k)))) :=
  projective_freeYoneda_base k

variable [HasExt.{w} (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (F : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})

example (n : ℕ) (x : (cohomologyPresheaf.{w, u + 1} F (n + 1)).obj
    (op (base (Spec (.of k))))) : x = 0 :=
  cohomologyPresheaf_succ_base_eq_zero k F n x

example [HasDerivedCategory.{w'}
      (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (n : ℕ)
    (x : (hypercohomologyPresheaf.{w', u + 1} (nisnevichTopology (Spec (.of k)))
      ((CochainComplex.singleFunctor _ 0).obj F) ((n + 1 : ℕ) : ℤ)).obj
        (op (base (Spec (.of k))))) : x = 0 := by
  let e := singleHypercohomologyEquivCohomology.{w, w', u + 1}
    (nisnevichTopology (Spec (.of k))) F (n + 1) (base (Spec (.of k)))
  apply e.injective
  exact (cohomologyPresheaf_succ_base_eq_zero k F n (e x)).trans (map_zero e).symm

end BaseField

end
