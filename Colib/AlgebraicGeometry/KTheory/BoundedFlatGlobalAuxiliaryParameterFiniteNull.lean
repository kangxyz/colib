/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterCoefficientNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFiberBassTower
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedGradedBassTower
public import Colib.KTheory.Bass.StrictDiagramIndexRowMapNaturality


/-! # The original auxiliary G7 null under every finite integral Spec-row comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Actual finite comparison preserves every original auxiliary full-open null value. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterFiniteNull.lean:29"
  "adaptation" "Original auxiliary actual Spec comparisons and the unchanged selected whole null"]
theorem finite_fullNull_square (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ) (s : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (ParameterAuxiliarySupport.fiber f.left T ⋙ prespectrumFunctor)).obj
        (specUnder.obj a)).space n) :
    ((StrictDiagramIndexRowMap.finiteMap specUnder (laurentUnderSquareFunctor _)
      squareFunctor specSquare (Functor.whiskerRight (openComparison f T) prespectrumFunctor)
        i).app a).map n
      (((strictDiagramIterateNull squareFunctor (ParameterAuxiliarySupport.fullNull f.left T)
        i).homotopy (specUnder.obj a)).level n (s, x)) =
      ((boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i).app a).map n
        (((boundedAboveFlatCoefficientSupportedFiberBassOpenNull f T i).homotopy a).level n
          (s, ((StrictDiagramIndexRowMap.finiteMap specUnder (laurentUnderSquareFunctor _)
      squareFunctor specSquare (Functor.whiskerRight (fiberComparison f T) prespectrumFunctor)
        i).app a).map n x)) := by
  have hp := strictDiagramIterateNull_level squareFunctor
    (ParameterAuxiliarySupport.fullNull f.left T) i (specUnder.obj a) n s x
  have hg := strictDiagramIterateNull_level (laurentUnderSquareFunctor _)
    (boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T) i a n s
    (((StrictDiagramIndexRowMap.finiteMap specUnder (laurentUnderSquareFunctor _)
      squareFunctor specSquare (Functor.whiskerRight (fiberComparison f T) prespectrumFunctor)
        i).app a).map n x)
  have h := congrArg (fun η => (η.app a).map n x)
    (StrictDiagramIndexRowMap.finiteMap_naturality specUnder (laurentUnderSquareFunctor _)
      squareFunctor specSquare
      (Functor.whiskerRight (fiberComparison f T) prespectrumFunctor)
      (Functor.whiskerRight (openComparison f T) prespectrumFunctor)
      (parameterNullTimeSlice f T s) (coefficientFullNullTimeSlice f T s)
      (fullNull_timeSlice_square f T s) i)
  simp only [coefficientFullNullTimeSlice, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.map_comp] at h
  exact (congrArg (fun y =>
    ((StrictDiagramIndexRowMap.finiteMap specUnder (laurentUnderSquareFunctor _)
      squareFunctor specSquare (Functor.whiskerRight (openComparison f T) prespectrumFunctor)
        i).app a).map n y) hp).trans
    (h.trans (congrArg
      (fun y => ((boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i).app a).map n y)
      hg.symm))

end AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
