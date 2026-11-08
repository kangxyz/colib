/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarUnitTrackTransport
public import Colib.Topology.Prespectrum.SelfTrackIntertwining
public import Colib.Topology.Prespectrum.SelfTrackStableNaturality
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperationIntertwining
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperationNaturality

/-!
# Original scalar restriction and flat-unit operations

The proved whole intertwining along the actual raw comparison Z, and separately along the
normalized comparison A, identifies the original finite and integer-graded operations. The
actual restriction map, every finite input, alternating sign and canonical reindexing are kept.
The original flat-unit canonical-null transport in `ScalarUnitTrackNull` remains separate.
It is not supplied by the scalar-cone canonical-null pasting constructed in this topic.
-/
/-! Implementation provenance:
    `Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarUnitTrackOperation.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole tracks, signs and
    independent parameters are retained. -/
@[expose] public section
open Topology SSet CategoryTheory.Functor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The actual raw comparison transports every finite input, including Pi-one at level zero. -/
theorem perfectOpenScalarOriginalOperation_restrict (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 1) ((originalPrespectrum (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace)).space n)
      ((originalPrespectrum (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).point n)) :
    HomotopyGroup.piMap (m + 1) ((perfectOpenScalarRestrictionMap j).map n)
        ((perfectOpenScalarRestrictionMap j).map_point n)
        ((perfectOpenScalarOriginalHomotopy j r q hq).homotopyClassOperation n m a) =
      (perfectFlatUnitHomotopy j q).homotopyClassOperation n m a := by
  rw [← Homotopy.homotopyClassOperation_postcomp]
  exact ((perfectOpenScalarOriginalHomotopy j r q hq).postcomp
    (perfectOpenScalarRestrictionMap j)).homotopyClassOperation_intertwine
      (perfectFlatUnitHomotopy j q) (perfectOpenOriginalRestrictionFlatHomotopy j)
      (perfectOpenScalarOriginalRestrictionUnitTrack j r q hq) n m a

/-- The separately normalized scalar track uses its original reversed-first comparison A. -/
theorem perfectOpenScalarOperation_restrict (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 1) ((originalPrespectrum (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace)).space n)
      ((originalPrespectrum (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).point n)) :
    HomotopyGroup.piMap (m + 1) ((perfectOpenScalarRestrictionMap j).map n)
        ((perfectOpenScalarRestrictionMap j).map_point n)
        ((perfectOpenScalarPrespectrumHomotopy j r q hq).homotopyClassOperation n m a) =
      (perfectFlatUnitHomotopy j q).homotopyClassOperation n m a := by
  rw [← Homotopy.homotopyClassOperation_postcomp]
  exact ((perfectOpenScalarPrespectrumHomotopy j r q hq).postcomp
    (perfectOpenScalarRestrictionMap j)).homotopyClassOperation_intertwine
      (perfectFlatUnitHomotopy j q) (perfectOpenRestrictionFlatHomotopy j)
      (perfectOpenScalarRestrictionUnitTrack j r q hq) n m a

/-- The raw stage keeps the exact alternating sign, integer degree and canonical tail offset. -/
theorem perfectOpenScalarOriginalCorrectedStage_restrict (d : ℤ) (n : ℕ) :
    ((-1 : ℤ) ^ n • (perfectOpenScalarOriginalHomotopy j r q hq).stableStageOperation d n) ≫
        (shiftedStableReindexIso (originalPrespectrum (perfectOpenWeakWaldhausen j)) d n).hom ≫
          (stableSystemMap (perfectOpenScalarRestrictionMap j) (d + 1)).app
            (parameterStableOffset d + n) =
      ((-1 : ℤ) ^ n • (perfectFlatUnitHomotopy j q).stableStageOperation d n) ≫
        (shiftedStableReindexIso (originalPrespectrum (RingedSpace.perfectComplexesWaldhausen
    U.toRingedSpace)) d n).hom := by
  exact ((perfectOpenScalarOriginalHomotopy j r q hq).correctedStableStageOperation_postcomp
    (perfectOpenScalarRestrictionMap j) d n).symm.trans
      (congrArg (fun k => ((-1 : ℤ) ^ n • k) ≫
        (shiftedStableReindexIso (originalPrespectrum (RingedSpace.perfectComplexesWaldhausen
    U.toRingedSpace)) d n).hom)
        (((perfectOpenScalarOriginalHomotopy j r q hq).postcomp
          (perfectOpenScalarRestrictionMap j)).stableStageOperation_intertwine
            (perfectFlatUnitHomotopy j q) (perfectOpenOriginalRestrictionFlatHomotopy j)
            (perfectOpenScalarOriginalRestrictionUnitTrack j r q hq) d n))

/-- The normalized stage retains the same sign and tail through its distinct actual comparison. -/
theorem perfectOpenScalarCorrectedStage_restrict (d : ℤ) (n : ℕ) :
    ((-1 : ℤ) ^ n • (perfectOpenScalarPrespectrumHomotopy j r q hq).stableStageOperation d n) ≫
        (shiftedStableReindexIso (originalPrespectrum (perfectOpenWeakWaldhausen j)) d n).hom ≫
          (stableSystemMap (perfectOpenScalarRestrictionMap j) (d + 1)).app
            (parameterStableOffset d + n) =
      ((-1 : ℤ) ^ n • (perfectFlatUnitHomotopy j q).stableStageOperation d n) ≫
        (shiftedStableReindexIso (originalPrespectrum (RingedSpace.perfectComplexesWaldhausen
    U.toRingedSpace)) d n).hom := by
  exact ((perfectOpenScalarPrespectrumHomotopy j r q hq).correctedStableStageOperation_postcomp
    (perfectOpenScalarRestrictionMap j) d n).symm.trans
      (congrArg (fun k => ((-1 : ℤ) ^ n • k) ≫
        (shiftedStableReindexIso (originalPrespectrum (RingedSpace.perfectComplexesWaldhausen
    U.toRingedSpace)) d n).hom)
        (((perfectOpenScalarPrespectrumHomotopy j r q hq).postcomp
          (perfectOpenScalarRestrictionMap j)).stableStageOperation_intertwine
            (perfectFlatUnitHomotopy j q) (perfectOpenRestrictionFlatHomotopy j)
            (perfectOpenScalarRestrictionUnitTrack j r q hq) d n))

/-- The raw scalar operation restricts to the actual flat-unit operation in every integer degree. -/
theorem perfectOpenScalarOriginalStableOperation_restrict (d : ℤ) :
    (perfectOpenScalarOriginalHomotopy j r q hq).stableOperation d ≫
        (stableHomotopyFunctor (d + 1)).map (perfectOpenScalarRestrictionMap j) =
      (perfectFlatUnitHomotopy j q).stableOperation d := by
  rw [← Homotopy.stableOperation_postcomp]
  exact ((perfectOpenScalarOriginalHomotopy j r q hq).postcomp
    (perfectOpenScalarRestrictionMap j)).stableOperation_intertwine
      (perfectFlatUnitHomotopy j q) (perfectOpenOriginalRestrictionFlatHomotopy j)
      (perfectOpenScalarOriginalRestrictionUnitTrack j r q hq) d

/-- The normalized scalar operation has its own comparison in every integer degree. -/
theorem perfectOpenScalarStableOperation_restrict (d : ℤ) :
    (perfectOpenScalarPrespectrumHomotopy j r q hq).stableOperation d ≫
        (stableHomotopyFunctor (d + 1)).map (perfectOpenScalarRestrictionMap j) =
      (perfectFlatUnitHomotopy j q).stableOperation d := by
  rw [← Homotopy.stableOperation_postcomp]
  exact ((perfectOpenScalarPrespectrumHomotopy j r q hq).postcomp
    (perfectOpenScalarRestrictionMap j)).stableOperation_intertwine
      (perfectFlatUnitHomotopy j q) (perfectOpenRestrictionFlatHomotopy j)
      (perfectOpenScalarRestrictionUnitTrack j r q hq) d

/-- The raw scalar K-operation restricts to the original unit operation, including K-zero. -/
theorem perfectOpenScalarOriginalKOperation_restrict (n : ℕ) :
    (KMap (perfectOpenRestrict_isExact j) (n + 1)).comp
        (originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (perfectOpenWeakWaldhausen j)
          (perfectOpenScalarOriginalHomotopy j r q hq) n) =
      originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)
        (perfectFlatUnitHomotopy j q) n := by
  rw [← originalKSelfTrackOperation_postcomp]
  exact originalKSelfTrackOperation_intertwine (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace) (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)
    ((perfectOpenScalarOriginalHomotopy j r q hq).postcomp (perfectOpenScalarRestrictionMap j))
    (perfectFlatUnitHomotopy j q) (perfectOpenOriginalRestrictionFlatHomotopy j)
    (perfectOpenScalarOriginalRestrictionUnitTrack j r q hq) n

/-- The normalized scalar K-operation retains its separate comparison on every original K-group. -/
theorem perfectOpenScalarKOperation_restrict (n : ℕ) :
    (KMap (perfectOpenRestrict_isExact j) (n + 1)).comp
        (originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (perfectOpenWeakWaldhausen j)
          (perfectOpenScalarPrespectrumHomotopy j r q hq) n) =
      originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)
        (perfectFlatUnitHomotopy j q) n := by
  rw [← originalKSelfTrackOperation_postcomp]
  exact originalKSelfTrackOperation_intertwine (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace) (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)
    ((perfectOpenScalarPrespectrumHomotopy j r q hq).postcomp
      (perfectOpenScalarRestrictionMap j))
    (perfectFlatUnitHomotopy j q) (perfectOpenRestrictionFlatHomotopy j)
    (perfectOpenScalarRestrictionUnitTrack j r q hq) n

end AlgebraicGeometry.Scheme.Modules

-- COL-0324 references
attribute [colib_ref "quillen"
  "PerfectComplexes/Spectrum/ScalarUnitTrackOperation.lean:1-144"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarOriginalOperation_restrict
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarOperation_restrict
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarOriginalCorrectedStage_restrict
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCorrectedStage_restrict
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarOriginalStableOperation_restrict
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarStableOperation_restrict
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarOriginalKOperation_restrict
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarKOperation_restrict

attribute [colib_tag "COL-0324"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarOriginalOperation_restrict
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarOriginalStableOperation_restrict
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarOriginalKOperation_restrict
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarKOperation_restrict
