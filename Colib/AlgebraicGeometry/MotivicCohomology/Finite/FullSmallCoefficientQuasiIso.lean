/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.FullSmallCoefficientModules
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.CoefficientQuotientQuasiIso

/-!
# Original finite cone comparison after actual full-small transport

The morphism is the image of the original cone-to-quotient map under the exact
change-of-topology and restriction functor. No Tate identification is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Cohomology.ZModSheaf

universe u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1}]

variable [HasSheafify (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable (X : SmoothSite (Spec (.of k)))

open CategoryTheory.Limits

/-- Actual coefficient transport preserves finite limits. -/
instance motivicFullSmallCoefficientTransport_preservesFiniteLimits :
    PreservesFiniteLimits (motivicFullSmallCoefficientTransport k X) := by
  unfold motivicFullSmallCoefficientTransport
  infer_instance

/-- Actual coefficient transport preserves finite colimits. -/
instance motivicFullSmallCoefficientTransport_preservesFiniteColimits :
    PreservesFiniteColimits (motivicFullSmallCoefficientTransport k X) := by
  unfold motivicFullSmallCoefficientTransport
  infer_instance

/-- The image of the original finite-cone-to-quotient comparison on the full small site. -/
def motivicFiniteFullSmallToCoefficientQuotient (q n : ℕ) :
    ((motivicFullSmallCoefficientTransport k X).mapHomologicalComplex (.up ℤ)).obj
        (motivicFiniteSheafComplex k q n) ⟶
      motivicCoefficientFullSmallEtaleComplex k X q n :=
  ((motivicFullSmallCoefficientTransport k X).mapHomologicalComplex (.up ℤ)).map
    (motivicFiniteToCoefficientQuotient k q n)

/-- The actual transported original comparison is a quasi-isomorphism. -/
theorem motivicFiniteFullSmallToCoefficientQuotient_quasiIso (q n : ℕ) (hn : n ≠ 0) :
    QuasiIso (motivicFiniteFullSmallToCoefficientQuotient k X q n) := by
  have : (motivicFullSmallCoefficientTransport k X).PreservesHomology := by infer_instance
  have := motivicFiniteToCoefficientQuotient_quasiIso k q n hn
  exact HomologicalComplex.quasiIso_map_of_preservesHomology
    (motivicFiniteToCoefficientQuotient k q n) (motivicFullSmallCoefficientTransport k X)

end AlgebraicGeometry.PresheafWithTransfers
