/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionLaurentAction
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientBassTelescope
public import Colib.KTheory.Bass.StrictDiagramMap
public import Colib.KTheory.Bass.ModelDiagramConnectivity
public import Colib.KTheory.Bass.ModelDiagramStableEquivalence
public import Colib.Topology.Prespectrum.TelescopeStableEquivalence

/-!
# The actual global-section to coefficient-section Bass telescope comparison

The source iterates its original base seed. The target is the existing native fine ambient
telescope. The unchanged restriction commutes strictly with those transitions and is stable
at every finite stage and on the actual quotient telescope.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The actual global row's original finite Bass iterates. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionTelescope.lean:32"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def globalDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (globalRow P ⋙ prespectrumFunctor)

/-- The original base scalar/null seed iterated at the same finite stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionTelescope.lean:37"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def globalTransition (i : ℕ) : globalDiagram P i ⟶ globalDiagram P (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R) (globalLaurentAction P).track.seed i

/-- The original global-row telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionTelescope.lean:41"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def globalTelescope : Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (globalDiagram P) (globalTransition P)

/-- The unchanged restriction at each finite stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionTelescope.lean:45"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def finiteRestriction (i : ℕ) :
    globalDiagram P i ⟶ boundedAboveFlatCoefficientAmbientBassDiagram P i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (Functor.whiskerRight (rowRestriction P) prespectrumFunctor)

/-- Original seed compatibility gives the exact finite transition square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionTelescope.lean:51"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem finiteRestriction_transition (i : ℕ) :
    finiteRestriction P i ≫ boundedAboveFlatCoefficientAmbientBassTransition P i =
      globalTransition P i ≫ finiteRestriction P (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (globalLaurentAction P).track.seed (boundedAboveFlatCoefficientAmbientBassSeed P)
    (Functor.whiskerRight (rowRestriction P) prespectrumFunctor)
    (rowRestriction_seed P) i).symm

/-- Actual restriction into the existing native fine ambient telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionTelescope.lean:60"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def telescopeRestriction :
    globalTelescope P ⟶ boundedAboveFlatCoefficientAmbientBassTelescopeFunctor P :=
  Telescope.diagramMap (globalDiagram P) (boundedAboveFlatCoefficientAmbientBassDiagram P)
    (globalTransition P) (boundedAboveFlatCoefficientAmbientBassTransition P)
    (finiteRestriction P) (finiteRestriction_transition P)

/-- Every original telescope cylinder retains its stage and full height. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionTelescope.lean:67"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem telescopeRestriction_cylinder (a : Under R) (n i : ℕ) (s : unitInterval)
    (x : ((globalDiagram P i).obj a).space n) :
    ((telescopeRestriction P).app a).map n
      (Telescope.cylinder (fun j => (globalDiagram P j).obj a)
        (fun j => (globalTransition P j).app a) n i (s, x)) =
    Telescope.cylinder (fun j => (boundedAboveFlatCoefficientAmbientBassDiagram P j).obj a)
      (fun j => (boundedAboveFlatCoefficientAmbientBassTransition P j).app a) n i
      (s, ((finiteRestriction P i).app a).map n x) :=
  Telescope.diagramMap_cylinder _ _ _ _ _ _ a n i s x

/-- Original stage inclusions commute with this same telescope map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionTelescope.lean:78"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem telescopeRestriction_inclusion (i : ℕ) :
    Telescope.diagramInclusion (globalDiagram P) (globalTransition P) i ≫
      telescopeRestriction P =
    finiteRestriction P i ≫ boundedAboveFlatCoefficientAmbientBassTelescopeInclusion P i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- Every original finite restriction is stable, using only its exact categorical inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionTelescope.lean:85"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem finiteRestriction_isStableEquivalence (i : ℕ) (a : Under R) :
    IsStableEquivalence ((finiteRestriction P i).app a) := by
  apply modelDiagramIterate_map_isStableEquivalence_of_exactEquivalence
    (laurentUnderSquareFunctor R) i (globalRow P)
    (boundedAboveFlatCoefficientSectionModelRow P) (rowRestriction P)
    (fun a => ((boundedAboveFlatGlobalCoefficientModelRestriction R).app (Opposite.op P,
      a)).hom.toFunctor.asEquivalence)
    (fun _ => rfl)
  exact fun a => boundedAboveFlatGlobalCoefficientRestriction_inverse_exact R (Opposite.op P, a)

/-- The actual natural telescope restriction is pointwise a stable equivalence. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionTelescope.lean:95"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
theorem telescopeRestriction_isStableEquivalence (a : Under R) :
    IsStableEquivalence ((telescopeRestriction P).app a) := by
  let : ∀ i n, T1Space (((globalDiagram P i).obj a).space n) :=
    fun i n => modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (globalRow P) a n
  let : ∀ i n, T1Space (((boundedAboveFlatCoefficientAmbientBassDiagram P i).obj a).space n) :=
    fun i n => modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientSectionModelRow P) a n
  exact Telescope.map_isStableEquivalence
    (fun i => (globalDiagram P i).obj a) (fun i => (globalTransition P i).app a)
    (fun i => (boundedAboveFlatCoefficientAmbientBassDiagram P i).obj a)
    (fun i => (boundedAboveFlatCoefficientAmbientBassTransition P i).app a)
    (fun i => (finiteRestriction P i).app a)
    (fun i => congrArg (fun η => η.app a) (finiteRestriction_transition P i))
    (fun i => finiteRestriction_isStableEquivalence P i a)

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex


namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

attribute [colib_tag "COL-0579"] telescopeRestriction_isStableEquivalence

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
