/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientSeedCompatibility
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionTelescope
public import Colib.KTheory.Bass.StrictDiagramIndexRowTelescope

/-! # The actual original integral Spec-to-fine comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open GlobalSupportedSection
open GlobalSectionChangeIndex

/-- The actual parameter telescope uses only the original scalar/null seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterCoefficientTelescope.lean:27"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
def parameterTelescope (Q : Scheme.{u}) : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u + 1} :=
  StrictDiagramIndexChange.telescope squareFunctor
    (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q))

/-- Realize the original full Model row isomorphism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterCoefficientTelescope.lean:32"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
def rowSpectrumIso (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    specUnder ⋙ parameterDiagram Q ≅ globalRow Q ⋙ prespectrumFunctor :=
  Functor.isoWhiskerRight (parameterRowModelIso Q) prespectrumFunctor

/-- The actual original seed supplies the sole transition input of index-plus-row descent. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterCoefficientTelescope.lean:37"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
theorem seed_square_row (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    Functor.whiskerLeft specUnder
        (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left)) ≫
      (StrictDiagramIndexChange.iso specUnder _ squareFunctor specSquare
        (parameterDiagram Q)).hom ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor _)).map (rowSpectrumIso Q).hom =
        (rowSpectrumIso Q).hom ≫ (globalLaurentAction Q).track.seed := by
  exact seed_square Q

/-- Every finite stage is the actual index comparison followed by the iterated Model row iso. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterCoefficientTelescope.lean:47"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
def finiteIso (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (i : ℕ) :
    specUnder ⋙ (strictDiagramIterate squareFunctor i).obj (parameterDiagram Q) ≅
      globalDiagram Q i :=
  StrictDiagramIndexRow.finiteIso specUnder _ squareFunctor specSquare (rowSpectrumIso Q) i

/-- The entire original parameter telescope restricts to the original global coefficient tower. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterCoefficientTelescope.lean:53"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
def telescopeIso (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    specUnder ⋙ parameterTelescope Q.left ≅ globalTelescope Q :=
  StrictDiagramIndexRow.telescopeIso specUnder _ squareFunctor specSquare (rowSpectrumIso Q)
    (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left))
    (globalLaurentAction Q).track.seed (seed_square_row Q)

/-- The actual Spec-row telescope comparison is stable because it has the displayed inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterCoefficientTelescope.lean:60"
  "adaptation" "Actual Spec row, whole original scalar/null seed, finite and telescope maps"]
theorem telescopeIso_stable (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((telescopeIso Q).hom.app a) := by
  intro d
  infer_instance

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient

