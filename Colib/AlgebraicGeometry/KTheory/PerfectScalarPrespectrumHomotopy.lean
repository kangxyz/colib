/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberSequenceMap
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopy

/-!
# The actual normalized scalar prespectrum track

The actual maps, whole tracks, signs and independent parameters are retained.
-/
/-! Implementation provenance:
    `Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarUnitTrack.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole tracks, signs and
    independent parameters are retained. -/
@[expose] public section
open Topology SSet CategoryTheory.Functor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
    CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum
open scoped Topology Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
variable (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
/-- The literal scalar gives its original canonically rebased whole self-track. -/
def perfectOpenScalarPrespectrumHomotopy :
    Homotopy (exactOriginalPrespectrumMap _ _ (changeWeak_exact (perfectOpenNested j)))
      (exactOriginalPrespectrumMap _ _ (changeWeak_exact (perfectOpenNested j))) :=
  exactOriginalPrespectrumHomotopy (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (perfectOpenWeakWaldhausen j)
    (changeWeak_exact (perfectOpenNested j)) (changeWeak_exact (perfectOpenNested j))
    (perfectGlobalScalar X r) (fun K => quasiIso_restrict_complexGlobalScalar j r q hq K.obj)


end AlgebraicGeometry.Scheme.Modules

-- COL-0324 references
attribute [colib_ref "quillen"
  "PerfectComplexes/Spectrum/ScalarUnitTrack.lean:1-113"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarPrespectrumHomotopy

attribute [colib_tag "COL-0324"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarPrespectrumHomotopy
