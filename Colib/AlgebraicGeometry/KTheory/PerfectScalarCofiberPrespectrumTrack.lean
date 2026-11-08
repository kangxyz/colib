/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarTrackNormalization
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberProjectionTrack
public import Colib.Topology.Prespectrum.RelativeHomotopyHorizontal

/-!
# The whole scalar inclusion and projection prespectrum triangle

The actual maps, whole tracks, signs and independent parameters are retained.
-/
/-! Implementation provenance:
    `Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberProjectionTrack.lean`
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
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)
local notation "hF" => changeWeak_exact (perfectOpenNested j)
variable (r : Γ(X, ⊤))
local notation "hM" =>
  Additivity.IsCofibrationSequence.exactG (perfectOpenScalarCofibrationSequence j r)
/-- The original coarse prespectrum projection, retaining the full old fine projection. -/
def perfectOpenScalarProjectionHomotopy :
    Homotopy (exactOriginalPrespectrumMap V W hM) (exactOriginalPrespectrumMap V W hF) :=
  exactOriginalPrespectrumHomotopy V W hM hF (perfectScalarProjectionNat X r)
    (perfectScalarProjectionNat_openWeak j r)

/-- Every point of the projection's first level is the original ordinary cylinder. -/
theorem perfectOpenScalarProjectionHomotopy_level_one (t : unitInterval) (x : (V).Delooping) :
    (perfectOpenScalarProjectionHomotopy j r).level 1
        (t, (V).asSmallDeloopingHomeomorph x) =
      (W).asSmallDeloopingHomeomorph
        (perfectOpenScalarProjectionRealizationHomotopy j r (t, x)) :=
  originalPrespectrumTransformationHomotopy_level_one V W _ _ _ _ _ _ t x
variable (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
/-- The actual canonically rebased coarse inclusion cylinder. -/
def perfectOpenScalarInclusionRealizationHomotopy :
    (deloopingMap (hF).rebase).hom.Homotopy (deloopingMap (hM).rebase).hom :=
  weakNaturalTransformationRealizationHomotopy V W (hF).rebase (hM).rebase
    (normalizedWeakTransformation hF hM (perfectScalarInclusionNat X r))
    (normalizedWeakTransformation_weak hF hM (perfectScalarInclusionNat X r)
      (perfectScalarInclusionNat_openWeak j r q hq))

/-- The original inclusion at every prespectrum level, with those same endpoint normalizations. -/
def perfectOpenScalarInclusionHomotopy :
    Homotopy (exactOriginalPrespectrumMap V W hF) (exactOriginalPrespectrumMap V W hM) :=
  exactOriginalPrespectrumHomotopy V W hF hM (perfectScalarInclusionNat X r)
    (perfectScalarInclusionNat_openWeak j r q hq)

/-- Every point of the inclusion's first level is its entire original ordinary cylinder. -/
theorem perfectOpenScalarInclusionHomotopy_level_one (t : unitInterval) (x : (V).Delooping) :
    (perfectOpenScalarInclusionHomotopy j r q hq).level 1
        (t, (V).asSmallDeloopingHomeomorph x) =
      (W).asSmallDeloopingHomeomorph
        (perfectOpenScalarInclusionRealizationHomotopy j r q hq (t, x)) :=
  originalPrespectrumTransformationHomotopy_level_one V W _ _ _ _ _ _ t x

/-- The old composition triangle has the actual scalar as its long edge. -/
def perfectOpenScalarProjectionCompositionTrack :
    (perfectOpenScalarPrespectrumHomotopy j r q hq).RelHomotopy
      ((perfectOpenScalarInclusionHomotopy j r q hq).trans
        (perfectOpenScalarProjectionHomotopy j r)) := by
  have J := exactOriginalPrespectrumCompositionHomotopy V W hF hM hF
    (perfectScalarInclusionNat X r) (perfectScalarProjectionNat X r)
    (perfectScalarInclusionNat_openWeak j r q hq) (perfectScalarProjectionNat_openWeak j r)
  convert J using 1 <;>
    simp only [perfectScalarInclusionNat_projection, perfectOpenScalarPrespectrumHomotopy,
      perfectOpenScalarInclusionHomotopy, perfectOpenScalarProjectionHomotopy]
  rfl

/-- The raw scalar retains the actual normalization prefix and the named association. -/
def perfectOpenScalarRawProjectionIntertwining :
    ((perfectOpenScalarOriginalHomotopy j r q hq).trans
      (perfectOpenChangeWeakNormalizationHomotopy j)).RelHomotopy
      ((perfectOpenChangeWeakNormalizationHomotopy j).trans
        ((perfectOpenScalarInclusionHomotopy j r q hq).trans
          (perfectOpenScalarProjectionHomotopy j r))) :=
  (perfectOpenScalarNormalizationTrack j r q hq).trans
    ((Homotopy.RelHomotopy.refl (perfectOpenChangeWeakNormalizationHomotopy j)).hcomp
      (perfectOpenScalarProjectionCompositionTrack j r q hq))

end AlgebraicGeometry.Scheme.Modules

-- COL-0324 references
attribute [colib_ref "quillen"
  "PerfectComplexes/Spectrum/ScalarCofiberProjectionTrack.lean:1-182"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarProjectionHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarProjectionHomotopy_level_one
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarInclusionRealizationHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarInclusionHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarInclusionHomotopy_level_one
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarProjectionCompositionTrack
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarRawProjectionIntertwining

attribute [colib_tag "COL-0324"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarProjectionCompositionTrack
