/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.Hypercohomology

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open AlgebraicGeometry.PresheafWithTransfers
universe w u
variable (k : Type u) [Field k]
-- These checks use the actual objects without assuming sheafification instances.
example (q : ℕ) : CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  motivicBaseComplex k q

example [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (p : ℤ) (q : ℕ) :
    motivicCohomology k p q (SmoothSite.base (Spec (.of k))) ≃+
      (motivicBaseComplex k q).homology p :=
  motivicBaseEvaluationComparison k p q

example [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (p : ℤ) (q : ℕ) {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y)
    (x : motivicCohomology k p q Y) :
    motivicCohomologyRestriction k p q f x =
      (DerivedCategory.singleFunctor _ 0).map
        ((Stacks.Cohomology.FreeYonedaUnivLE.freeYoneda.{u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k)))).map f) ≫ x :=
  motivicCohomologyRestriction_apply k p q f x

variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1}]

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

example (p : ℤ) (q : ℕ) :
    motivicCohomology k p q (SmoothSite.base (Spec (.of k))) ≃+
      (motivicBaseComplex k q).homology p :=
  motivicBaseEvaluationComparison k p q

example (p : ℤ) (q : ℕ) (X : SmoothSite (Spec (.of k))) :
    motivicCohomologyRestriction k p q (𝟙 X) = 𝟙 _ :=
  motivicCohomologyRestriction_id k p q X

example (p : ℤ) (q : ℕ) {X Y Z : SmoothSite (Spec (.of k))}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    motivicCohomologyRestriction k p q (f ≫ g) =
      motivicCohomologyRestriction k p q g ≫ motivicCohomologyRestriction k p q f :=
  motivicCohomologyRestriction_comp k p q f g

example (q : ℕ) (i j : ℤ) :
    (motivicBaseComplex k q).d i j =
      ((motivicSheafComplex k q).d i j).hom.app
        (op (SmoothSite.base (Spec (.of k)))) :=
  motivicBaseComplex_d k q i j
