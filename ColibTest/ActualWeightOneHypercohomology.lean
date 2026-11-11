/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.Hypercohomology

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers AlgebraicGeometry.MotivicCohomology.WeightOne
open Stacks.Cohomology.FreeYonedaUnivLE

universe w w' u

noncomputable section

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w}
    (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

example (p : ℤ) : motivicCohomologyPresheaf.{w, u} k p 1 ≅
    hypercohomologyPresheaf.{w, u + 1} (nisnevichTopology (Spec (.of k)))
      ((CochainComplex.singleFunctor _ 0).obj (largeUnitsSheaf (Spec (.of k)))) (p - 1) :=
  weightOneHypercohomologyPresheafIso k p

example : motivicCohomologyPresheaf.{w, u} k (-2) 1 ≅
    hypercohomologyPresheaf.{w, u + 1} (nisnevichTopology (Spec (.of k)))
      ((CochainComplex.singleFunctor _ 0).obj (largeUnitsSheaf (Spec (.of k)))) (-3) :=
  weightOneHypercohomologyPresheafIso k (-2)

example (p : ℤ) {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    (motivicCohomologyPresheaf.{w, u} k p 1).map f.op ≫
        (weightOneHypercohomologyPresheafIso k p).hom.app (op X) =
      (weightOneHypercohomologyPresheafIso k p).hom.app (op Y) ≫
        (hypercohomologyPresheaf.{w, u + 1} (nisnevichTopology (Spec (.of k)))
          ((CochainComplex.singleFunctor _ 0).obj (largeUnitsSheaf (Spec (.of k))))
          (p - 1)).map f.op :=
  weightOneHypercohomologyPresheafIso_naturality k p f

variable [HasExt.{w'}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

example (n : ℕ) (X : SmoothSite (Spec (.of k))) :
    motivicCohomology.{w, u} k ((n : ℤ) + 1) 1 X ≃+
      (cohomologyPresheaf.{w', u + 1} (largeUnitsSheaf (Spec (.of k))) n).obj (op X) :=
  weightOneSheafCohomologyEquiv k n X

example (X : SmoothSite (Spec (.of k))) :
    motivicCohomology.{w, u} k 1 1 X ≃+
      (cohomologyPresheaf.{w', u + 1} (largeUnitsSheaf (Spec (.of k))) 0).obj (op X) :=
  weightOneSheafCohomologyEquiv k 0 X
