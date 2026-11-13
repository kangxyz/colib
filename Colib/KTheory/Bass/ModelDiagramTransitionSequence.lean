/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.ModelDiagramTwoChartStableSequence
public import Colib.KTheory.Bass.StrictDiagramSuccessorTransition

/-!
Source: `Quillen/KTheory/Bass/ModelDiagramTransitionSequence.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Actual inter-stage morphisms of the finite Model Bass rows

The original strict seed and its iterated images act on all four corners of the unchanged
Laurent square. Their actual spectral row map has the original quotient and right-kernel
components. Its middle component is the next original transition under the genuine
right-iteration endpoint transports.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory CategoryTheory.Limits Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
universe u w
namespace KTheory.Bass

variable {R : CommRingCat.{u}}
    (F : Under R ⥤ WideSubcategory preservesZero.{w})
    (η : F ⋙ prespectrumFunctor ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj (F ⋙ prespectrumFunctor))
    (i : ℕ) (a : Under R)

/-- The original iterated transition acts on the original Laurent square, corner by corner. -/
def modelDiagramTransitionSquareMap :
    modelDiagramTwoChartSquare F i a ⟶ modelDiagramTwoChartSquare F (i + 1) a :=
  ((Functor.mapArrowFunctor (Arrow (Under R)) (Arrow LoopPrespectrum.{w})).map
    ((Functor.mapArrowFunctor (Under R) LoopPrespectrum.{w}).map
      (strictDiagramTransition (laurentUnderSquareFunctor R) η i))).app
        (laurentUnderSquare R a)

/-- The unchanged transition gives an actual map between the original finite-stage Bass rows. -/
def modelDiagramTransitionSequenceMap (d : ℤ) :
    modelDiagramTwoChartSequence F i a d ⟶ modelDiagramTwoChartSequence F (i + 1) a d :=
  KTheory.Bass.TwoChartStable.bassSequenceMap (modelDiagramTransitionSquareMap F η i a)
    (modelDiagramTwoChartSpectralConditions F i a)
    (modelDiagramTwoChartSpectralConditions F (i + 1) a) d

/-- The first component is exactly the original chart-quotient map of the four-corner transition.
-/
theorem modelDiagramTransitionSequenceMap_left (d : ℤ) :
    (modelDiagramTransitionSequenceMap F η i a d).τ₁ =
      KTheory.Bass.TwoChartStable.chartCokernelMap
        (modelDiagramTransitionSquareMap F η i a) (d + 1) := rfl

/-- The final component is the original kernel map induced by the same transition square. -/
theorem modelDiagramTransitionSequenceMap_right (d : ℤ) :
    (modelDiagramTransitionSequenceMap F η i a d).τ₃ =
      KTheory.Bass.TwoChartStable.bassRightMap
        (modelDiagramTransitionSquareMap F η i a) d := rfl

/-- The middle component is the original Bass image of the previous strict transition. -/
theorem modelDiagramTransitionSequenceMap_middle (d : ℤ) :
    (modelDiagramTransitionSequenceMap F η i a d).τ₂ =
      (stableHomotopyFunctor d).map
        (((strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (strictDiagramTransition (laurentUnderSquareFunctor R) η i)).app a) := rfl

/-- The original successor transition is precisely this middle map with genuine endpoint
transports, rather than an unrelated isomorphic map. -/
theorem modelDiagramTransitionSequenceMap_middle_successor (d : ℤ) :
    (stableHomotopyFunctor d).map
      ((strictDiagramTransition (laurentUnderSquareFunctor R) η (i + 1)).app a) ≫
        (stableHomotopyFunctor d).map
          ((eqToHom (congrArg
            (fun H : (Under R ⥤ LoopPrespectrum.{w}) ⥤ (Under R ⥤ LoopPrespectrum.{w}) =>
              H.obj (F ⋙ prespectrumFunctor))
            (strictDiagramIterate_succ_right (laurentUnderSquareFunctor R) (i + 1)))).app a) =
      (stableHomotopyFunctor d).map
        ((eqToHom (congrArg
          (fun H : (Under R ⥤ LoopPrespectrum.{w}) ⥤ (Under R ⥤ LoopPrespectrum.{w}) =>
            H.obj (F ⋙ prespectrumFunctor))
          (strictDiagramIterate_succ_right (laurentUnderSquareFunctor R) i))).app a) ≫
        (modelDiagramTransitionSequenceMap F η i a d).τ₂ := by
  rw [modelDiagramTransitionSequenceMap_middle, ← Functor.map_comp, ← Functor.map_comp]
  apply congrArg ((stableHomotopyFunctor d).map)
  exact congrArg (fun t => t.app a)
    (strictDiagramTransition_succ_right (laurentUnderSquareFunctor R) η i)

end KTheory.Bass
