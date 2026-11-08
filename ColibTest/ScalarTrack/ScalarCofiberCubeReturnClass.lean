/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberReturnRestriction


/-! # Original whole scalar composition, signed return and K-operation clients -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
open Topology SSet
open Topology SSet CategoryTheory.Functor

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
    AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
    CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open scoped Topology Simplicial
universe u
namespace ColibTest.ScalarTrack.ScalarCofiberCubeReturnClass
local instance scalarReturnClassTestCoproducts (X : Scheme.{u}) :
    HasBinaryCoproducts (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
    X.toRingedSpace))) := Additivity.hasBinaryCoproducts (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|
    (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)
local notation "af" => scalarFineAdditivitySourceCube X (𝟙 (𝟭 (ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
  (QuotientRows.oneIdToZero V) (perfectScalarIdentityFineCofibrationSequence (X := X)) n p
local notation "b" => perfectOpenScalarCubeChangeWeak j n af
local notation "pSmall" => GenLoop.postcomp
  (ContinuousMap.HomotopyEquiv.toFun (Homeomorph.toHomotopyEquiv
    (Structure.asSmallDeloopingHomeomorph (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace))))
  (Structure.asSmallDeloopingHomeomorph_basepoint (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace))
  (perfectScalarProjectionInputCube n p)

/-- The original inclusion edge keeps its full ordinary realization time and source cube. -/
theorem original_inclusion (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarFineCubeInclusionPath j r q hq n p t z =
      perfectOpenScalarInclusionRealizationHomotopy j r q hq
        (t, separatedFirstDeloopingMap V (p z)) :=
  perfectOpenScalarFineCubeInclusionPath_ordinary j r q hq n p t z

/-- The projection uses the original fine path before forward small-model transport. -/
theorem original_projection (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    (perfectOpenScalarProjectionHomotopy j r).genLoopPath 1 pSmall t z =
      (W).asSmallDeloopingHomeomorph
        (perfectOpenScalarCubeChangeWeak j n
          (perfectOpenScalarFineProjectionCubePath j r n p t) z) :=
  perfectOpenScalarFineProjectionCubePath_smallModel_apply j r n p t z

/-- The whole composition retains both original halves for arbitrary track and spatial times. -/
theorem original_composition (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    ((perfectOpenScalarInclusionHomotopy j r q hq).trans
        (perfectOpenScalarProjectionHomotopy j r)).genLoopPath 1 pSmall t z =
      (W).asSmallDeloopingHomeomorph
        (perfectOpenScalarCubeCompositionPath j r q hq n p t z) :=
  perfectOpenScalarCubeCompositionPath_smallModel_apply j r q hq n p t z

include r q hq in
/-- The source equality targets the actual canonically rebased exact map. -/
theorem original_normalized_endpoint :
    GenLoop.postcomp (W).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun
        (W).asSmallDeloopingHomeomorph_basepoint b =
      GenLoop.postcomp
        ((exactOriginalPrespectrumMap V W (changeWeak_exact (perfectOpenNested j))).map 1)
        ((exactOriginalPrespectrumMap V W (changeWeak_exact (perfectOpenNested j))).map_point 1)
        pSmall :=
  perfectOpenScalarCubeCompositionPath_smallModel_endpoint j r q hq n p

/-- Both endpoint casts use the symmetry of that actual time-zero equality. -/
theorem original_whole_cast_path :
    ((perfectOpenScalarCubeCompositionPath j r q hq n p).map
      (genLoopPostcompContinuousMap (W).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun
        (W).asSmallDeloopingHomeomorph_basepoint).continuous).cast
          (perfectOpenScalarCubeCompositionPath_smallModel_endpoint j r q hq n p).symm
          (perfectOpenScalarCubeCompositionPath_smallModel_endpoint j r q hq n p).symm =
      ((perfectOpenScalarInclusionHomotopy j r q hq).trans
        (perfectOpenScalarProjectionHomotopy j r)).genLoopPath 1 pSmall :=
  perfectOpenScalarCubeCompositionPath_smallModel j r q hq n p

/-- The whole comparison is exactly the original triangle evaluated on the unchanged cube. -/
theorem original_whole_triangle_data :
    perfectOpenScalarCompositionCubeHomotopy j r q hq n p =
      (perfectOpenScalarProjectionCompositionTrack j r q hq).genLoopPathHomotopy 1 n pSmall :=
  perfectOpenScalarCompositionCubeHomotopy_eq j r q hq n p

/-- Both independent times and every spatial coordinate retain that literal original data. -/
theorem original_two_triangle_data (a t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCompositionCubeHomotopy j r q hq n p (a, t) z =
      Homotopy.RelHomotopy.genLoopPathHomotopy
        (perfectOpenScalarProjectionCompositionTrack j r q hq) 1 n pSmall (a, t) z :=
  perfectOpenScalarCompositionCubeHomotopy_data_apply j r q hq n p a t z

/-- The negative level-one sign is exactly one inverse of the entire composition class. -/
theorem original_composition_inverse :
    originalKSelfTrackOperation V W (perfectOpenScalarPrespectrumHomotopy j r q hq) n
        (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n) =
      (genLoopSelfTrackClass n b (perfectOpenScalarCubeCompositionPath j r q hq n p))⁻¹ :=
  perfectOpenScalarKOperation_compositionCube j r q hq n p

/-- The literal signed return, including the unchanged quotient-first and identity edges. -/
theorem original_signed_return :
    genLoopSelfTrackClass n b
        (((perfectOpenScalarFineCubeReturn j r n p).map
          (perfectOpenScalarCubeChangeWeak j n).continuous).trans
            (perfectOpenScalarFineCubeTerminalWord j r q hq n p)) =
      originalKSelfTrackOperation V W (perfectOpenScalarPrespectrumHomotopy j r q hq) n
        (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n) :=
  perfectOpenScalarCubeReturn_class j r q hq n p

/-- The distinct raw scalar operation is reached by the actual normalization intertwining. -/
theorem original_raw_scalar :
    genLoopSelfTrackClass n b
        (((perfectOpenScalarFineCubeReturn j r n p).map
          (perfectOpenScalarCubeChangeWeak j n).continuous).trans
            (perfectOpenScalarFineCubeTerminalWord j r q hq n p)) =
      originalKSelfTrackOperation V W (perfectOpenScalarOriginalHomotopy j r q hq) n
        (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n) :=
  perfectOpenScalarCubeReturn_originalClass j r q hq n p

/-- The actual restriction map lands on the actual flat-unit track's operation. -/
theorem original_flat_unit_restriction :
    KMap (perfectOpenRestrict_isExact j) (n + 1)
        (genLoopSelfTrackClass n b
          (((perfectOpenScalarFineCubeReturn j r n p).map
            (perfectOpenScalarCubeChangeWeak j n).continuous).trans
              (perfectOpenScalarFineCubeTerminalWord j r q hq n p))) =
      originalKSelfTrackOperation V (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)
    (perfectFlatUnitHomotopy j q) n
        (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n) :=
  perfectOpenScalarCubeReturn_class_restrict j r q hq n p

/-- Every original spatial boundary remains fixed at independent triangle and track times. -/
theorem original_triangle_boundary (a t : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarCompositionCubeHomotopy j r q hq n p (a, t) z =
      (originalPrespectrum W).point 1 :=
  (perfectOpenScalarCompositionCubeHomotopy j r q hq n p (a, t)).property z hz

/-- The raw comparison includes one-coordinate cubes, without dropping either return edge. -/
theorem original_degree_zero (p0 : GenLoop (Fin 1)
    |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|
    (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))) :
    genLoopSelfTrackClass 0
        (perfectOpenScalarCubeChangeWeak j 0
          (scalarFineAdditivitySourceCube X (𝟙 (𝟭 (ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
            (QuotientRows.oneIdToZero V)
            (perfectScalarIdentityFineCofibrationSequence (X := X)) 0 p0))
        (((perfectOpenScalarFineCubeReturn j r 0 p0).map
          (perfectOpenScalarCubeChangeWeak j 0).continuous).trans
            (perfectOpenScalarFineCubeTerminalWord j r q hq 0 p0)) =
      originalKSelfTrackOperation V W (perfectOpenScalarOriginalHomotopy j r q hq) 0
        (⟦perfectScalarProjectionInputCube 0 p0⟧ : (V).K 0) :=
  perfectOpenScalarCubeReturn_originalClass j r q hq 0 p0

end ColibTest.ScalarTrack.ScalarCofiberCubeReturnClass
