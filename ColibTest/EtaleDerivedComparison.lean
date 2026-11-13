/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.Finite.EtaleDerivedComparison

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers

universe u w w'

noncomputable section

variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasSheafify (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w'}
  (Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

-- The domain is the original existing group; the two derived universes are independent.
example (p : ℤ) (q n : ℕ) (X : SmoothSite (Spec (.of k))) :
    motivicFiniteCohomology k p q n X →+ motivicFiniteEtaleCohomology k p q n X :=
  motivicFiniteEtaleCohomologyComparison k p q n X

-- Negative cohomological degrees are not silently truncated to natural numbers.
example (q n : ℕ) (X : SmoothSite (Spec (.of k))) :
    motivicFiniteCohomology k (-1) q n X →+ motivicFiniteEtaleCohomology k (-1) q n X :=
  motivicFiniteEtaleCohomologyComparison k (-1) q n X
