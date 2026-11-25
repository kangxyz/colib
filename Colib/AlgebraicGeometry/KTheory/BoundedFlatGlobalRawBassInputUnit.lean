/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputCharts
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassStep
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectUnitTrackComposition
public import Colib.Topology.Prespectrum.RelativeHomotopyIntertwining

/-!
# Forward Laurent units across the original global raw input square

The actual forward Laurent coordinate is preserved by geometric pullback. Its original unit
homotopies intertwine with the entire original split Laurent projection square.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Every actual scheme map preserves the original pulled-back forward Laurent coordinate. -/
theorem laurentUnit_map :
    Units.map (laurent.map g).appTop.hom.toMonoidHom
      (laurentScalar (op Y)) =
      laurentScalar (op X) :=
  laurentScalar_map g.op

namespace InputUnit

/-- The original source-fiber Laurent projection composition track. -/
def oldComposition :=
  boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy
    (laurent.map g) (laurentProjection.app Y)

/-- The original target-fiber track with its genuine scheme-arrow-square endpoint transport. -/
def newComposition :=
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy (laurentProjection.app X)
    g).cast
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap
      (laurentProjection.naturality g)).symm rfl

/-- The common actual pulled-back forward unit on the original composite map. -/
def commonUnit :=
  boundedAboveFlatPerfectUnitHomotopy
    (laurent.map g ≫ laurentProjection.app Y)
    (laurentScalar (op X))

/-- The original old unit loop followed by the actual Laurent scheme-arrow map. -/
def oldUnit :=
  (unitHomotopy Y).postcomp
    (boundedAboveFlatPerfectPullbackPrespectrumMap (laurent.map g))

/-- The original target unit loop preceded by the actual base scheme-arrow map. -/
def newUnit :=
  Homotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap g)
    (unitHomotopy X)

/-- Exact scalar transport preserves the entire old projection-unit comparison. -/
def oldComparison :
    ((oldComposition g).trans (oldUnit g)).RelHomotopy
      ((commonUnit g).trans (oldComposition g)) := by
  have J := boundedAboveFlatPerfectUnitTrackPostcomp
    (laurent.map g) (laurentProjection.app Y)
    (laurentScalar (op Y))
  simpa only [oldComposition, oldUnit, commonUnit, unitHomotopy,
    laurentUnit_map] using J

/-- The new projection-unit comparison keeps the actual scheme-square transport. -/
def newComparison :
    ((newComposition g).trans (newUnit g)).RelHomotopy
      ((commonUnit g).trans (newComposition g)) := by
  refine (boundedAboveFlatPerfectUnitTrackPrecomp (laurentProjection.app X) g
    (laurentScalar (op X))).ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    apply Homotopy.trans_level_congr
    · exact congrArg (fun q ↦ (boundedAboveFlatPerfectUnitHomotopy q
        (laurentScalar (op X))).level n)
        (laurentProjection.naturality g)
    · rfl

/-- The two specified projection comparisons intertwine the unchanged forward unit loops. -/
def squarePasting :
    ((oldUnit g).trans ((oldComposition g).symm.trans (newComposition g))).RelHomotopy
      (((oldComposition g).symm.trans (newComposition g)).trans (newUnit g)) :=
  Homotopy.RelHomotopy.intertwine _ _ _ _ _ (oldComparison g) (newComparison g)

end InputUnit

/-- The existing outer Laurent square retains both complete original composition tracks. -/
theorem laurentSquareHomotopy_level (n : ℕ) :
    (laurentSquareHomotopy g).level n =
      ((InputUnit.oldComposition g).symm.trans
        (InputUnit.newComposition g)).level n :=
  rfl

/-- The original forward-unit loops intertwine across the whole actual Laurent square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalRawBassInputUnit.lean:107-121"
  "adaptation" "Original forward Laurent-unit pasting for an arbitrary scheme arrow"]
def laurentUnitPasting :
    ((InputUnit.oldUnit g).trans
      (laurentSquareHomotopy g)).RelHomotopy
    ((laurentSquareHomotopy g).trans
      (InputUnit.newUnit g)) := by
  refine (InputUnit.squarePasting g).ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr
    · rfl
    · exact laurentSquareHomotopy_level g n
  · intro n
    apply Homotopy.trans_level_congr
    · exact laurentSquareHomotopy_level g n
    · rfl

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass
