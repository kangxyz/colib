/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumUnitRoutes
public import Colib.Topology.Prespectrum.HomotopySquareOfPasting
public import Colib.Topology.Prespectrum.HomotopySquarePathPasting
public import Colib.Topology.Prespectrum.PushoutIdentityFromUnitSquare
public import Colib.Topology.Prespectrum.RelativeHomotopyPasting

/-! # The original geometric unit square for bounded-flat pullback

Rotating the actual relative unit-route comparison gives the whole original commuting
square. Both boundary tracks are the original split geometric units, and the opposite
track is the literal constant identity.

Implementation provenance: `Quillen/AlgebraicGeometry/PerfectComplexes/`
`Spectrum/BoundedFlatPullback.lean:51-62`, `BoundedFlat/SquareTrackCompatibility.lean:28-39`
and `BoundedFlat/OriginalUnitSquare.lean:65-84` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules

local notation "K(" f ")" => boundedAboveFlatPerfectPullbackPrespectrumMap f

/-- Reverse the first actual composition track and follow the second after endpoint transport. -/
def boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy {X Y Z T : Scheme.{u}}
    (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
    (h : p ≫ v = q ≫ w) :
    Homotopy (K(v) ≫ K(p)) (K(w) ≫ K(q)) :=
  (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy p v).symm.trans
    ((boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy q w).cast
      (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap h).symm rfl)

/-- The original geometric square, with both full unit tracks and independent parameters. -/
def boundedAboveFlatPerfectPullbackPrespectrumUnitSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy
      (𝟙 X) f f (𝟙 Y) (by simp only [Category.id_comp, Category.comp_id])).Square
      (coneSquareIdentityTrack K(f))
      (Homotopy.precomp K(f) (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X))
      ((boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy Y).postcomp K(f)) := by
  let L := (Homotopy.precomp K(f)
    (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X)).cast rfl (Category.comp_id _)
  let M := ((boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy Y).postcomp K(f)).cast
    rfl (Category.id_comp _)
  have J := Homotopy.RelHomotopy.rotate (boundedAboveFlatPerfectOriginalUnitRoutesComparison f)
  have J' := J.trans
    ((Homotopy.RelHomotopy.transRefl L).symm.hcomp (Homotopy.RelHomotopy.refl M.symm))
  have S := J'.toSquare
  refine S.ofBoundaryLevels _ _ _ _ ?_ (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  intro n
  unfold boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy
  apply Homotopy.trans_level_congr <;> rfl

end AlgebraicGeometry.Scheme.Modules
