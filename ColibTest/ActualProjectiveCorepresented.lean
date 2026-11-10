/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Algebra.Homology.DerivedCategory.ProjectiveCorepresented

open CategoryTheory Opposite Stacks.Cohomology.Corepresented

universe w v u

section

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  (T : A ⥤ AddCommGrpCat.{v}) [T.Additive] (Z : A) [Projective Z]
  (e : preadditiveCoyoneda.obj (op Z) ≅ T)
  {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ)

example (x : ((T.mapHomologicalComplex (.up ℤ)).obj K).homology n) :
    projectiveHomologyDerivedAddEquiv T Z e L n
        (HomologicalComplex.homologyMap ((T.mapHomologicalComplex (.up ℤ)).map f) n x) =
      projectiveHomologyDerivedAddEquiv T Z e K n x ≫ (DerivedCategory.Q.map f)⟦n⟧' :=
  projectiveHomologyDerivedAddEquiv_naturality T Z e f n x

example (K : CochainComplex A ℤ) (n : ℤ)
    (x : ((T.mapHomologicalComplex (.up ℤ)).obj K).homology n) :
    (projectiveHomologyDerivedAddEquiv T Z e K n).symm
      (projectiveHomologyDerivedAddEquiv T Z e K n x) = x :=
  AddEquiv.symm_apply_apply _ x

end

#print axioms Stacks.Cohomology.Corepresented.projectiveHomologyDerivedAddEquiv
#print axioms Stacks.Cohomology.Corepresented.projectiveHomologyDerivedAddEquiv_naturality
