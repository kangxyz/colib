/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.Finite.EtaleBockstein

/-! Signed consecutive-degree regressions on the original finite and integral motivic groups. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers

universe w w' u

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

example (q : ℕ) (a : motivicFiniteCohomology k (-2) q 6 X) :
    motivicEtaleCohomologyComparison k (-2 + 1) q X
      (motivicCohomologyBockstein k (-2) q 6 X a) =
    motivicEtaleCohomologyBockstein k (-2) q 6 X
      (motivicFiniteEtaleCohomologyComparison k (-2) q 6 X a) :=
  motivicFiniteEtaleCohomologyComparison_bockstein k (-2) q 6 X a

example (q : ℕ) : motivicCohomologyBockstein k (-1) q 0 X 0 = 0 := map_zero _

example (q : ℕ) (a b : motivicFiniteCohomology k 1 q 6 X) :
    motivicCohomologyBockstein k 1 q 6 X (a + b) =
      motivicCohomologyBockstein k 1 q 6 X a + motivicCohomologyBockstein k 1 q 6 X b :=
  map_add _ _ _

example (q : ℕ) (a : motivicFiniteEtaleCohomology k (-1) q 0 X) :
    motivicEtaleCohomologyBockstein k (-1) q 0 X a =
      (a ≫ (DerivedCategory.Q.map (motivicFiniteEtaleSheafComplexIso k q 0).hom)⟦(-1 : ℤ)⟧') ≫
        CochainComplex.finiteCoefficients.derivedBockstein (motivicEtaleSheafComplex k q) 0 (-1) :=
  motivicEtaleCohomologyBockstein_eq k (-1) q 0 X a
