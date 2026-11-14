/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.MotivicCohomology.Finite.MilnorDiagonal
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme PresheafWithTransfers
open AlgebraicGeometry.MotivicCohomology.FiniteMilnorDiagonal
universe w u
variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1}]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

example : milnorModulo k 0 0 ≃+
    motivicFiniteCohomology k 0 0 0 (SmoothSite.base (Spec (.of k))) :=
  motivicFiniteEquiv k 0 0
example : milnorModulo k 0 6 ≃+
    motivicFiniteCohomology k 0 0 6 (SmoothSite.base (Spec (.of k))) :=
  motivicFiniteEquiv k 0 6
example : milnorModulo k 1 1 ≃+
    motivicFiniteCohomology k 1 1 1 (SmoothSite.base (Spec (.of k))) :=
  motivicFiniteEquiv k 1 1
example : milnorModulo k 1 6 ≃+
    motivicFiniteCohomology k 1 1 6 (SmoothSite.base (Spec (.of k))) :=
  motivicFiniteEquiv k 1 6
example : milnorModulo k 2 6 ≃+
    motivicFiniteCohomology k 2 2 6 (SmoothSite.base (Spec (.of k))) :=
  motivicFiniteEquiv k 2 6
