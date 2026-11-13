/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientNull
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedParameterCoefficientTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterIteratedFullNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionLocalizationFiniteNull
public import Colib.KTheory.Bass.StrictDiagramIndexRowNaturality

/-!
# The original full-open null under every finite integral Spec-row comparison

Each original null time is an actual natural transformation. The proved whole
base square therefore passes through the original finite index and row
isomorphisms, retaining both the chosen null and every prespectrum level.
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
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The literal time slice of the original full-open parameter null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterFiniteNull.lean:37"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
def parameterFullNullTimeSlice (s : unitInterval) :
    ParameterModels.supported f.left ⋙ prespectrumFunctor ⟶
      ParameterModels.ambient P.left ⋙ prespectrumFunctor :=
  diagramHomotopyAt
    (η := Functor.whiskerRight (ParameterModels.forget f.left) prespectrumFunctor ≫
      ParameterFullCurrentNull.fullMap f.left)
    (θ := diagramZeroMap (ParameterModels.supported f.left ⋙ prespectrumFunctor)
      (ParameterModels.ambient P.left ⋙ prespectrumFunctor))
    (ParameterFullCurrentNull.fullNull f.left).homotopy
    (ParameterFullCurrentNull.fullNull f.left).naturality s

/-- The original full-time row square is an exact square of original time-slice maps. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterFiniteNull.lean:49"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem fullNull_timeSlice_row (s : unitInterval) :
    Functor.whiskerLeft specUnder (parameterFullNullTimeSlice f s) ≫ (rowSpectrumIso P).hom =
      (GlobalSupportedParameterCoefficient.rowSpectrumIso f).hom ≫
        (globalSupportedOpenNullTimeSlice f s ≫
          Functor.whiskerRight (globalOpenRestriction f) prespectrumFunctor) := by
  apply NatTrans.ext
  funext a
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact fullNull_row_square f a n s x

/-- Actual finite index comparison preserves every original full-open null value. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterFiniteNull.lean:63"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem finite_fullNull_square (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ) (s : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (ParameterModels.supported f.left ⋙ prespectrumFunctor)).obj (specUnder.obj a)).space n) :
    ((finiteIso P i).hom.app a).map n
      (((strictDiagramIterateNull squareFunctor (ParameterFullCurrentNull.fullNull f.left)
        i).homotopy (specUnder.obj a)).level n (s, x)) =
      ((FullOpenTelescope.finiteRestriction f i).app a).map n
        (((globalSupportedOpenFiniteNull f i).homotopy a).level n
          (s, ((GlobalSupportedParameterCoefficient.finiteIso f i).hom.app a).map n x)) := by
  have hp := strictDiagramIterateNull_level squareFunctor
    (ParameterFullCurrentNull.fullNull f.left) i (specUnder.obj a) n s x
  have hg := strictDiagramIterateNull_level (laurentUnderSquareFunctor _)
    (globalSupportedOpenNull f) i a n s
    (((GlobalSupportedParameterCoefficient.finiteIso f i).hom.app a).map n x)
  have h := congrArg (fun η => (η.app a).map n x)
    (StrictDiagramIndexRow.finiteIso_naturality specUnder (laurentUnderSquareFunctor _)
      squareFunctor specSquare (GlobalSupportedParameterCoefficient.rowSpectrumIso f)
      (rowSpectrumIso P) (parameterFullNullTimeSlice f s)
      (globalSupportedOpenNullTimeSlice f s ≫
        Functor.whiskerRight (globalOpenRestriction f) prespectrumFunctor)
      (fullNull_timeSlice_row f s) i)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp] at h
  exact (congrArg (fun y => ((finiteIso P i).hom.app a).map n y) hp).trans
    (h.trans (congrArg (fun y => ((FullOpenTelescope.finiteRestriction f i).app a).map n y)
      hg.symm))

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient

