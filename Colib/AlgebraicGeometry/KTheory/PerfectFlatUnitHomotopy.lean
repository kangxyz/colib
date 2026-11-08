/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.PerfectFlatPullback
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopy

/-!
# The actual flat-pullback unit prespectrum track

The actual maps, whole tracks, signs and independent parameters are retained.
-/
/-! Implementation provenance: `Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/GlobalUnit.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole tracks, signs and
    independent parameters are retained. -/
@[expose] public section
open Topology SSet CategoryTheory.Functor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
    CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
/-- The actual normalized spectrum map of a genuinely flat geometric morphism. -/
def perfectFlatPrespectrumMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    originalPrespectrum (RingedSpace.perfectComplexesWaldhausen Y.toRingedSpace) ⟶
    originalPrespectrum (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) :=
  exactOriginalPrespectrumMap _ _ (perfectFlatPullback_waldhausenExact f)

/-- An original global unit gives the full structure-compatible self-homotopy of flat pullback. -/
def perfectFlatUnitHomotopy {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (r : (Γ(X, ⊤))ˣ) :
    LoopPrespectrum.Homotopy (perfectFlatPrespectrumMap f) (perfectFlatPrespectrumMap f) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (perfectFlatPullback_waldhausenExact f)
    (perfectFlatPullback_waldhausenExact f) (perfectFlatPullbackUnitIso f r)

end AlgebraicGeometry.Scheme.Modules

-- COL-0324 references
attribute [colib_ref "quillen"
  "PerfectComplexes/Spectrum/GlobalUnit.lean:1-60"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectFlatPrespectrumMap
  AlgebraicGeometry.Scheme.Modules.perfectFlatUnitHomotopy
