/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberFineCubeEdges
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberProjectionTrack
public import Colib.KTheory.Waldhausen.Additivity.SeparatedPairMap

/-! # The original fine projection on the actual subdivision cube

The projection uses the same coarse-rebased endpoints, viewed as fine exact. Its whole image
is the original coarse projection cylinder. Actual diagonal naturality identifies its endpoints
with the two fine additivity sources before the literal path is cast. No ordinary triangle or
canonical-sum endpoint is supplied here.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberFineProjectionCubePath.lean:34-152`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, universes,
normalizations, time coordinates and spatial boundaries are retained. -/
@[expose] public section
open Topology SSet

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
  CategoryTheory.Waldhausen.Fibration
open scoped Simplicial Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (r : Γ(X, ⊤))
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)
local notation "hF" => changeWeak_exact (perfectOpenNested j)
local notation "hM" =>
  IsCofibrationSequence.exactG (perfectOpenScalarCofibrationSequence j r)

/-- The same coarse-rebased middle has the original fine chosen zero. -/
theorem perfectOpenScalarProjectionMiddle_zero :
    (CategoryTheory.rebaseFunctor (perfectScalarMiddleFunctor X r) (V).zero (W).zero
      (((hM).zero (V).isZero).iso (W).isZero)).obj (V).zero = (V).zero :=
  (CategoryTheory.rebaseFunctor_obj_base _ _ _ _).trans (perfectOpenNested j).zero_eq

/-- The same coarse-rebased identity has that same original fine zero. -/
theorem perfectOpenScalarProjectionIdentity_zero :
    (CategoryTheory.rebaseFunctor (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
      (X := X.toRingedSpace)))) (V).zero (W).zero
      (((hF).zero (V).isZero).iso (W).isZero)).obj (V).zero = (V).zero :=
  (CategoryTheory.rebaseFunctor_obj_base _ _ _ _).trans (perfectOpenNested j).zero_eq

/-- Every time of the literal fine projection cylinder fixes the original chosen zero. -/
theorem perfectOpenScalarProjectionFine_zero (t : unitInterval) :
    perfectOpenScalarProjectionFineRealizationHomotopy j r (t, (V).kBasepoint) =
      (V).kBasepoint :=
  weakNaturalTransformationRealizationHomotopy_fixed_zero V V
    (perfectOpenScalarMiddleRebase_fineExact j r)
    (perfectOpenScalarIdentityRebase_fineExact j)
    (normalizedWeakTransformation hM hF (perfectScalarProjectionNat X r))
    (perfectOpenScalarNormalizedProjection_fineWeak j r)
    (perfectOpenScalarProjectionMiddle_zero j r)
    (perfectOpenScalarProjectionIdentity_zero j) t

variable (n : ℕ) (p : GenLoop (Fin (n + 1))
  |SSet.diagonalSSet
    (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (RingedSpace.perfectComplexesWaldhausen
      X.toRingedSpace))|
  (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))

/-- The original horizontal endpoint and actual diagonal iso on the supplied cube. -/
def perfectScalarProjectionInputCube : GenLoop (Fin (n + 1)) (V).Delooping (V).kBasepoint :=
  GenLoop.postcomp (separatedFirstDeloopingMap V) (separatedFirstDeloopingMap_basepoint V) p

/-- The literal source cube of the same-rebase fine projection. -/
def perfectOpenScalarProjectionMiddleCube :
    GenLoop (Fin (n + 1)) (V).Delooping (V).kBasepoint :=
  GenLoop.postcomp (deloopingMap (perfectOpenScalarMiddleRebase_fineExact j r)).hom
    (deloopingMap_basepoint_of_zeroEq (perfectOpenScalarMiddleRebase_fineExact j r)
      (perfectOpenScalarProjectionMiddle_zero j r)) (perfectScalarProjectionInputCube n p)

/-- The literal target cube of the same-rebase fine projection. -/
def perfectOpenScalarProjectionIdentityCube :
    GenLoop (Fin (n + 1)) (V).Delooping (V).kBasepoint :=
  GenLoop.postcomp (deloopingMap (perfectOpenScalarIdentityRebase_fineExact j)).hom
    (deloopingMap_basepoint_of_zeroEq (perfectOpenScalarIdentityRebase_fineExact j)
      (perfectOpenScalarProjectionIdentity_zero j)) (perfectScalarProjectionInputCube n p)

/-- Curry the whole original fine projection before changing its endpoint presentation. -/
def perfectOpenScalarProjectionCubePath :
    Path (perfectOpenScalarProjectionMiddleCube j r n p)
      (perfectOpenScalarProjectionIdentityCube j n p) :=
  genLoopPathOfHomotopyRel (GenLoop.postcompHomotopy
    (deloopingMap_basepoint_of_zeroEq (perfectOpenScalarMiddleRebase_fineExact j r)
      (perfectOpenScalarProjectionMiddle_zero j r))
    (deloopingMap_basepoint_of_zeroEq (perfectOpenScalarIdentityRebase_fineExact j)
      (perfectOpenScalarProjectionIdentity_zero j))
    (perfectOpenScalarProjectionFineRealizationHomotopy j r)
    (perfectOpenScalarProjectionFine_zero j r) (perfectScalarProjectionInputCube n p))

/-- Actual diagonal naturality identifies the scalar fine source with the projection source. -/
theorem perfectOpenScalarProjectionMiddleCube_eq :
    scalarFineAdditivitySourceCube X (perfectScalarInclusionNat X r)
        (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) n p =
      perfectOpenScalarProjectionMiddleCube j r n p := by
  ext z
  exact DFunLike.congr_fun
    (realizedDiagonalMap_exact_naturality V V
      (IsCofibrationSequence.exactG (perfectScalarCofibrationSequence X r)).rebase)
    (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)) (p z))

/-- The identity fine source is the same actual normalized projection target. -/
theorem perfectOpenScalarProjectionIdentityCube_eq :
    scalarFineAdditivitySourceCube X (𝟙 (𝟭 (ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))) (QuotientRows.oneIdToZero V)
        (perfectScalarIdentityFineCofibrationSequence (X := X)) n p =
      perfectOpenScalarProjectionIdentityCube j n p := by
  ext z
  exact DFunLike.congr_fun
    (realizedDiagonalMap_exact_naturality V V
      (IsCofibrationSequence.exactG
        (perfectScalarIdentityFineCofibrationSequence (X := X))).rebase)
    (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)) (p z))

/-- The original fine projection with precisely the two fine additivity source endpoints. -/
def perfectOpenScalarFineProjectionCubePath :
    Path (scalarFineAdditivitySourceCube X (perfectScalarInclusionNat X r)
      (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) n p)
      (scalarFineAdditivitySourceCube X (𝟙 (𝟭 (ObjectProperty.FullSubcategory
        (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))) (QuotientRows.oneIdToZero V)
        (perfectScalarIdentityFineCofibrationSequence (X := X)) n p) :=
  (perfectOpenScalarProjectionCubePath j r n p).cast
    (perfectOpenScalarProjectionMiddleCube_eq j r n p)
    (perfectOpenScalarProjectionIdentityCube_eq j n p)

/-- Every original projection time and spatial coordinate is retained by the endpoint casts. -/
theorem perfectOpenScalarFineProjectionCubePath_apply (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarFineProjectionCubePath j r n p t z =
      perfectOpenScalarProjectionFineRealizationHomotopy j r
        (t, separatedFirstDeloopingMap V (p z)) := rfl

/-- The entire original coarse projection is the actual image of this fine path. -/
theorem perfectOpenScalarFineProjectionCubePath_changeWeak (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCubeChangeWeak j n (perfectOpenScalarFineProjectionCubePath j r n p t) z =
      perfectOpenScalarProjectionRealizationHomotopy j r
        (t, separatedFirstDeloopingMap V (p z)) :=
  perfectOpenScalarProjectionRealizationHomotopy_changeWeak j r t
    (separatedFirstDeloopingMap V (p z))

/-- Every time retains the entire original spatial boundary, including one input coordinate. -/
theorem perfectOpenScalarFineProjectionCubePath_boundary (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarFineProjectionCubePath j r n p t z = (V).kBasepoint :=
  (perfectOpenScalarFineProjectionCubePath j r n p t).property z hz

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0317",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberFineProjectionCubePath.lean:34-152"
    "adaptation"
    "Actual scalar normalization and canonical fiber maps on the unchanged subdivision cube"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineProjectionCubePath_apply
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineProjectionCubePath_changeWeak
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineProjectionCubePath_boundary
