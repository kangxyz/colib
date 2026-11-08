/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarUnitTrackOperation


/-! Actual raw scalar finite input, negative stage sign/tail and unchanged colimit leg. -/
public section
open Topology SSet
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Topology AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
universe u
namespace ColibTest.ScalarTrack.ScalarUnitTrackOperation
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The actual finite theorem retains the original input Pi-one at level zero. -/
theorem original_zero_finite
    (a : HomotopyGroup.Pi 1 ((originalPrespectrum (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace)).space 0)
      ((originalPrespectrum (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).point 0)) :
    HomotopyGroup.piMap 1 ((perfectOpenScalarRestrictionMap j).map 0)
        ((perfectOpenScalarRestrictionMap j).map_point 0)
        ((perfectOpenScalarOriginalHomotopy j r q hq).homotopyClassOperation 0 0 a) =
      (perfectFlatUnitHomotopy j q).homotopyClassOperation 0 0 a :=
  perfectOpenScalarOriginalOperation_restrict j r q hq 0 0 a

/-- The degree-minus-one client retains the exact sign, unsimplified shift and canonical tail. -/
theorem original_negative_stage (n : ℕ) :
    ((-1 : ℤ) ^ n • (perfectOpenScalarOriginalHomotopy j r q hq).stableStageOperation (-1) n) ≫
        (shiftedStableReindexIso (originalPrespectrum (perfectOpenWeakWaldhausen j)) (-1) n).hom ≫
          (stableSystemMap (perfectOpenScalarRestrictionMap j) ((-1) + 1)).app
            (parameterStableOffset (-1) + n) =
      ((-1 : ℤ) ^ n • (perfectFlatUnitHomotopy j q).stableStageOperation (-1) n) ≫
        (shiftedStableReindexIso (originalPrespectrum (RingedSpace.perfectComplexesWaldhausen
    U.toRingedSpace)) (-1) n).hom :=
  perfectOpenScalarOriginalCorrectedStage_restrict j r q hq (-1) n

/-- Every original colimit stage leg sees the same raw-to-flat comparison in every degree. -/
theorem original_stage_leg (d : ℤ) (n : ℕ) :
    stableHomotopyι (originalPrespectrum (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))
    d n ≫
        ((perfectOpenScalarOriginalHomotopy j r q hq).stableOperation d ≫
          (stableHomotopyFunctor (d + 1)).map (perfectOpenScalarRestrictionMap j)) =
      stableHomotopyι (originalPrespectrum (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace)) d n ≫
        (perfectFlatUnitHomotopy j q).stableOperation d := by
  rw [perfectOpenScalarOriginalStableOperation_restrict]
  rfl

/-- Every original K-zero class keeps the raw scalar operation and actual restriction map. -/
theorem original_raw_kzero (a : (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K 0) :
    KMap (perfectOpenRestrict_isExact j) 1
        (originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (perfectOpenWeakWaldhausen j)
          (perfectOpenScalarOriginalHomotopy j r q hq) 0 a) =
      originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)
        (perfectFlatUnitHomotopy j q) 0 a :=
  DFunLike.congr_fun (perfectOpenScalarOriginalKOperation_restrict j r q hq 0) a

/-- The normalized K-operation is separately tested on every original class and degree. -/
theorem original_normalized_kmap (n : ℕ) (a : (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace).K n) :
    KMap (perfectOpenRestrict_isExact j) (n + 1)
        (originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (perfectOpenWeakWaldhausen j)
          (perfectOpenScalarPrespectrumHomotopy j r q hq) n a) =
      originalKSelfTrackOperation (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)
        (perfectFlatUnitHomotopy j q) n a :=
  DFunLike.congr_fun (perfectOpenScalarKOperation_restrict j r q hq n) a

end ColibTest.ScalarTrack.ScalarUnitTrackOperation
