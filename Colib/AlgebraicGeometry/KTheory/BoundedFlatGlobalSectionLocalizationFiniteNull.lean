/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionLocalizationNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedBassTower
/-! # The original complete finite null and independent Laurent/seed times -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
open CategoryTheory.Functor.IdentityAutomorphism
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- An actual time slice of the unchanged global null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionLocalizationFiniteNull.lean:25"
  "adaptation" "Original whole localization-null time slices and independent seed action"]
def globalSupportedOpenNullTimeSlice (s : unitInterval) :
    supportedRow f ⋙ prespectrumFunctor ⟶ openRow f ⋙ prespectrumFunctor :=
  diagramHomotopyAt
    (η := Functor.whiskerRight (supportedRowForget f) prespectrumFunctor ≫
      Functor.whiskerRight (openRowChangeWeak f) prespectrumFunctor)
    (θ := diagramZeroMap (supportedRow f ⋙ prespectrumFunctor)
      (openRow f ⋙ prespectrumFunctor))
    (globalSupportedOpenNull f).homotopy (globalSupportedOpenNull f).naturality s

/-- The entire original null time slice commutes with the actual restriction maps. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionLocalizationFiniteNull.lean:35"
  "adaptation" "Original whole localization-null time slices and independent seed action"]
theorem globalSupportedOpenNull_timeSlice (s : unitInterval) :
    globalSupportedOpenNullTimeSlice f s ≫
      Functor.whiskerRight (openRowRestriction f) prespectrumFunctor =
    Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor ≫
      boundedAboveFlatCoefficientSupportedOpenNullTimeSlice f s := by
  apply NatTrans.ext
  funext a
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact globalSupportedOpenNull_restriction f a n s x

/-- Iterate the original global null without selecting a new track. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionLocalizationFiniteNull.lean:49"
  "adaptation" "Original whole localization-null time slices and independent seed action"]
def globalSupportedOpenFiniteNull (i : ℕ) :=
  strictDiagramIterateNull (laurentUnderSquareFunctor R) (globalSupportedOpenNull f) i

/-- Every finite-stage restriction retains all original null times and level values. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionLocalizationFiniteNull.lean:53"
  "adaptation" "Original whole localization-null time slices and independent seed action"]
theorem globalSupportedOpenFiniteNull_restriction (i : ℕ) (a : Under R) (n : ℕ)
    (s : unitInterval)
    (x : (((strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
      (supportedRow f ⋙ prespectrumFunctor)).obj a).space n) :
    (((strictDiagramIterate (laurentUnderSquareFunctor R) i).map
        (Functor.whiskerRight (openRowRestriction f) prespectrumFunctor)).app a).map n
      (((globalSupportedOpenFiniteNull f i).homotopy a).level n (s, x)) =
    ((boundedAboveFlatCoefficientSupportedBassOpenNull f i).homotopy a).level n
      (s, (((strictDiagramIterate (laurentUnderSquareFunctor R) i).map
        (Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor)).app a).map n x) := by
  have hG := strictDiagramIterateNull_level (laurentUnderSquareFunctor R)
    (globalSupportedOpenNull f) i a n s x
  have hF := strictDiagramIterateNull_level (laurentUnderSquareFunctor R)
    (boundedAboveFlatCoefficientSupportedOpenDiagramNull f) i a n s
    ((((strictDiagramIterate (laurentUnderSquareFunctor R) i).map
      (Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor)).app a).map n x)
  have h := congrArg (fun η =>
    (((strictDiagramIterate (laurentUnderSquareFunctor R) i).map η).app a).map n x)
      (globalSupportedOpenNull_timeSlice f s)
  simp only [Functor.map_comp, NatTrans.comp_app] at h
  exact (congrArg (fun y =>
    (((strictDiagramIterate (laurentUnderSquareFunctor R) i).map
      (Functor.whiskerRight (openRowRestriction f) prespectrumFunctor)).app a).map n y) hG).trans
        (h.trans hF.symm)

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

