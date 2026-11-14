/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.Finite.FullSmallEtaleComparison

/-! Literal finite-source regressions with independent derived universes. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers

universe w w' w'' u

variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1}]

variable [HasSheafify (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w'}
  (Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

variable (X : SmoothSite (Spec (.of k)))
variable [HasDerivedCategory.{w''} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]

example (q : ℕ) :
    motivicFiniteFullSmallEtaleCohomologyComparison k X (-1) q 0 0 = 0 :=
  map_zero _

example (q : ℕ) (a b : motivicFiniteCohomology k (-2) q 6 X) :
    motivicFiniteFullSmallEtaleCohomologyComparison k X (-2) q 6 (a + b) =
      motivicFiniteFullSmallEtaleCohomologyComparison k X (-2) q 6 a +
      motivicFiniteFullSmallEtaleCohomologyComparison k X (-2) q 6 b :=
  map_add _ _ _
