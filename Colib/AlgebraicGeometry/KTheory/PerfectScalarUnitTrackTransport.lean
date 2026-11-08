/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarUnitTrack
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarTrackNormalization
public import Colib.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# Actual raw scalar restriction and flat-unit transport

The actual maps, whole tracks, signs and independent parameters are retained.
-/
/-! Implementation provenance:
    `Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarUnitTrackTransport.lean`
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
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
/-- The raw comparison retains B postcomposed by restriction, followed by C inverse then D. -/
def perfectOpenOriginalRestrictionFlatHomotopy :
    Homotopy
      (changeWeakPrespectrumMap (perfectOpenNested j) ≫ perfectOpenScalarRestrictionMap j)
      (perfectFlatPrespectrumMap j) :=
  ((perfectOpenChangeWeakNormalizationHomotopy j).postcomp
    (perfectOpenScalarRestrictionMap j)).trans (perfectOpenRestrictionFlatHomotopy j)

variable (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
/-- The two original scalar routes intertwine along the entire specified raw-to-flat comparison. -/
def perfectOpenScalarOriginalRestrictionUnitTrack :
    (((perfectOpenScalarOriginalHomotopy j r q hq).postcomp
      (perfectOpenScalarRestrictionMap j)).trans
        (perfectOpenOriginalRestrictionFlatHomotopy j)).RelHomotopy
      ((perfectOpenOriginalRestrictionFlatHomotopy j).trans (perfectFlatUnitHomotopy j q)) := by
  let H0 := (perfectOpenScalarOriginalHomotopy j r q hq).postcomp
    (perfectOpenScalarRestrictionMap j)
  let H1 := (perfectOpenScalarPrespectrumHomotopy j r q hq).postcomp
    (perfectOpenScalarRestrictionMap j)
  let B := (perfectOpenChangeWeakNormalizationHomotopy j).postcomp
    (perfectOpenScalarRestrictionMap j)
  let A := perfectOpenRestrictionFlatHomotopy j
  let Hq := perfectFlatUnitHomotopy j q
  have JB : (H0.trans B).RelHomotopy (B.trans H1) := by
    have J := (perfectOpenScalarNormalizationTrack j r q hq).postcomp
      (perfectOpenScalarRestrictionMap j)
    simpa only [Homotopy.postcomp_trans] using J
  have JA : (H1.trans A).RelHomotopy (A.trans Hq) :=
    perfectOpenScalarRestrictionUnitTrack j r q hq
  exact (Homotopy.RelHomotopy.transAssoc H0 B A).symm.trans
    ((JB.hcomp (Homotopy.RelHomotopy.refl A)).trans
      ((Homotopy.RelHomotopy.transAssoc B H1 A).trans
        (((Homotopy.RelHomotopy.refl B).hcomp JA).trans
          (Homotopy.RelHomotopy.transAssoc B A Hq).symm)))

end AlgebraicGeometry.Scheme.Modules

-- COL-0324 references
attribute [colib_ref "quillen"
  "PerfectComplexes/Spectrum/ScalarUnitTrackTransport.lean:1-126"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenOriginalRestrictionFlatHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarOriginalRestrictionUnitTrack

attribute [colib_tag "COL-0324"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarOriginalRestrictionUnitTrack
