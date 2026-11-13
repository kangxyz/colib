/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.Finite.EtaleNaturality

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

example (p : ℤ) (q n : ℕ) {X Y : SmoothSite (Spec (.of k))} (g : X ⟶ Y)
    (a : motivicFiniteCohomology k p q n Y) :
    motivicFiniteEtaleCohomologyComparison k p q n X
        (motivicFiniteCohomologyRestriction k p q n g a) =
      motivicFiniteEtaleCohomologyRestriction k p q n g
        (motivicFiniteEtaleCohomologyComparison k p q n Y a) :=
  motivicFiniteEtaleCohomologyComparison_restriction k p q n g a
