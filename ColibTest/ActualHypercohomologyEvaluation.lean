/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.Sites.Hypercohomology.Evaluation

open CategoryTheory Opposite Stacks.Cohomology.FreeYonedaUnivLE

universe w t v u

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v t}]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{max u v t})]
  (X : C) [Projective ((freeYoneda.{max u t} J).obj X)]
  {K L : CochainComplex (Sheaf J AddCommGrpCat.{max u v t}) ℤ} (f : K ⟶ L)

example (n : ℤ) (x : (hypercohomologyPresheaf.{w, max u t} J K n).obj (op X)) :
    hypercohomologyEvaluationAddEquiv.{w, t} J X L n
      (((hypercohomologyPresheafFunctor.{w, max u t} J n).map f).app (op X) x) =
    HomologicalComplex.homologyMap
      ((((sheafSections J AddCommGrpCat.{max u v t}).obj (op X)).mapHomologicalComplex
        (.up ℤ)).map f) n (hypercohomologyEvaluationAddEquiv.{w, t} J X K n x) :=
  hypercohomologyEvaluationAddEquiv_naturality.{w, t} J X f n x

end

#print axioms Stacks.Cohomology.FreeYonedaUnivLE.hypercohomologyEvaluationAddEquiv
#print axioms Stacks.Cohomology.FreeYonedaUnivLE.hypercohomologyEvaluationAddEquiv_naturality
