/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Path.PointHEP
public import Colib.Topology.Prespectrum.ParameterLooping

/-!
# Well-based points of actual parameter-correct looping

At each original level, a closed chosen point with HEP remains well-based under
the unchanged compact-open parameter-looping construction. The independent
structure parameter and the actual loop-space basepoint are untouched.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/ParameterLoopingPointHEP.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original closed-singleton and point-HEP hypotheses are retained for the
actual compact-open loop-space basepoint at each unchanged prespectrum level. -/
@[expose] public section

noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum

/-- Original closed point HEP is preserved at each actual parameter-looping level. -/
theorem parameterLooping_point_homotopyExtensionProperty (E : LoopPrespectrum.{u}) (n : ℕ)
    (hc : IsClosed ({E.point n} : Set (E.space n)))
    (h : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point n)))) :
    TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} ((parameterLooping E).point n))) :=
  Path.homotopyExtensionProperty_refl hc h

end Topology.LoopPrespectrum
