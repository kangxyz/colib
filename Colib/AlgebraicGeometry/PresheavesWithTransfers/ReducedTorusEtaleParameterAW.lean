/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleTensor
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusOrdinaryDerivedProduct
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusCoordinateInsertion

/-! # The actual parameter-reindexed AW denominator

Coordinate insertion lands in the parameter reindexing of the diagonal tensor.
Its denominator is therefore reindexed AW, not AW itself. Reindexing is performed
on presheaves, where it is exact, before exact sheafification and localization.
No derived functor of sheaf parameter sections or invertibility of the one-way
sheafify/reindex comparison is asserted. Signed shifts and topology transport
must still be applied to the resulting concrete parameter-coordinate square.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "P" => SmoothEtaleIntegralPresheaves k
local notation "S" => SmoothEtaleIntegralSheaves k
local notation "a" => smoothEtaleIntegralSheafify k

/-- The original presheaf parameter reindexing used by coordinate insertion. -/
abbrev reducedTorusIntegralParameterReindex : P ⥤ P :=
  AlgebraicSimplex.parameterReindex k (A := ModuleCat.{u + 1} ℤ)
    (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k)))

/-- Presheaf parameter reindexing preserves homology, unlike an unproved claim
about the sheaf parameter-sections functor. -/
instance reducedTorusIntegralParameterReindex_preservesHomology :
    (reducedTorusIntegralParameterReindex k).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- Reindex the actual AW denominator before extending and sheafifying it. -/
instance reducedTorusEtaleParameterAW_quasiIso (q : ℕ) :
    QuasiIso (((a).mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap
        (((reducedTorusIntegralParameterReindex k).mapHomologicalComplex (.down ℕ)).map
          (reducedTorusPresheafAW k q)) ComplexShape.embeddingDownNat)) := by
  let : (a).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels a
  infer_instance

variable [HasDerivedCategory.{v} (SmoothEtaleIntegralSheaves k)]

/-- Parameter reindexing, extension, sheafification and localization, in that order. -/
def integralEtaleParameterChainToDerived : ChainComplex P ℕ ⥤ DerivedCategory S :=
  (reducedTorusIntegralParameterReindex k).mapHomologicalComplex (.down ℕ) ⋙
    ComplexShape.embeddingDownNat.extendFunctor _ ⋙
      (a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

/-- The denominator required by the coordinate-insertion roof is invertible. -/
instance reducedTorusEtaleParameterDerivedAW_isIso (q : ℕ) :
    IsIso ((integralEtaleParameterChainToDerived k).map (reducedTorusPresheafAW k q)) := by
  change IsIso (DerivedCategory.Q.map (((a).mapHomologicalComplex (.up ℤ)).map
    (HomologicalComplex.extendMap
      (((reducedTorusIntegralParameterReindex k).mapHomologicalComplex (.down ℕ)).map
        (reducedTorusPresheafAW k q)) ComplexShape.embeddingDownNat)))
  infer_instance

end AlgebraicGeometry.PresheafWithTransfers
