/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedParameterCoefficientSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalLocalizationTelescopeStable
public import Colib.KTheory.Bass.StrictDiagramIndexRowTelescope

/-!
# The actual supported integral Spec-row Bass telescope

The original supported seed square gives a natural isomorphism of entire iterated-seed
quotient telescopes. Its specified inverse comes from the actual index and Model row
isomorphisms. Composing with the existing supported restriction yields the stable comparison
to the unchanged original fine supported telescope.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection

/-- The original supported parameter telescope with its actual scalar/null seed. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientTelescope.lean:34"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
def parameterTelescope {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] :
    Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u + 1} :=
  StrictDiagramIndexChange.telescope squareFunctor
    (KTheory.Bass.SchemeNaturalSeed.seed (ParameterLaurentTrack.supportedTrack f))

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The complete actual supported Model row isomorphism on original prespectra. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientTelescope.lean:43"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
def rowSpectrumIso : specUnder ⋙ parameterDiagram f ≅ supportedRow f ⋙ prespectrumFunctor :=
  Functor.isoWhiskerRight (parameterSupportedRowIso f) prespectrumFunctor

/-- The original supported seed supplies the exact index-plus-row transition square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientTelescope.lean:47"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem seed_square_row :
    Functor.whiskerLeft specUnder
        (KTheory.Bass.SchemeNaturalSeed.seed (ParameterLaurentTrack.supportedTrack f.left)) ≫
      (StrictDiagramIndexChange.iso specUnder _ squareFunctor specSquare
        (parameterDiagram f)).hom ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor _)).map (rowSpectrumIso f).hom =
        (rowSpectrumIso f).hom ≫ (supportedLaurentAction f).track.seed := by
  exact seed_square f

/-- Every finite supported comparison is the original index iso and iterated Model row iso. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientTelescope.lean:57"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
def finiteIso (i : ℕ) :
    specUnder ⋙ (strictDiagramIterate squareFunctor i).obj (parameterDiagram f) ≅
      SupportedTelescope.globalDiagram f i :=
  StrictDiagramIndexRow.finiteIso specUnder _ squareFunctor specSquare (rowSpectrumIso f) i

/-- The entire supported parameter telescope is the original supported global coefficient tower. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientTelescope.lean:63"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
def telescopeIso : specUnder ⋙ parameterTelescope f.left ≅ SupportedTelescope.globalTelescope f :=
  StrictDiagramIndexRow.telescopeIso specUnder _ squareFunctor specSquare (rowSpectrumIso f)
    (KTheory.Bass.SchemeNaturalSeed.seed (ParameterLaurentTrack.supportedTrack f.left))
    (supportedLaurentAction f).track.seed (seed_square_row f)

/-- The actual supported Spec-row comparison has its specified stable inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientTelescope.lean:69"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem telescopeIso_stable (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((telescopeIso f).hom.app a) := by
  intro d
  infer_instance

/-- Actual Spec restriction followed by the original fine supported coefficient restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientTelescope.lean:75"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
def fineTelescopeComparison :
    specUnder ⋙ parameterTelescope f.left ⟶
      boundedAboveFlatCoefficientSupportedBassTelescopeFunctor f :=
  (telescopeIso f).hom ≫ SupportedTelescope.telescopeRestriction f

/-- The complete comparison to the original fine supported telescope is stable at each algebra. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientTelescope.lean:80"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem fineTelescopeComparison_stable (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((fineTelescopeComparison f).app a) :=
  (telescopeIso_stable f a).comp (SupportedTelescope.telescopeRestriction_isStableEquivalence f a)

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient

