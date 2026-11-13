/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.KTheory.Bass.StrictDiagramMap
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedAction
public import Colib.Topology.Prespectrum.TelescopeDiagramMap
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedBassTelescope
/-! # Original supported global telescope and unchanged restriction -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Functor.IdentityAutomorphism
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
namespace SupportedTelescope

/-- The actual global row's original finite Bass iterates. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedTelescope.lean:34"
  "adaptation" "Original global supported telescope with unchanged stage and whole height"]
def globalDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (supportedRow f ⋙ prespectrumFunctor)

/-- The original base scalar/null seed iterated at the same finite stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedTelescope.lean:39"
  "adaptation" "Original global supported telescope with unchanged stage and whole height"]
def globalTransition (i : ℕ) : globalDiagram f i ⟶ globalDiagram f (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R) (supportedLaurentAction f).track.seed i

/-- The original global-row telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedTelescope.lean:43"
  "adaptation" "Original global supported telescope with unchanged stage and whole height"]
def globalTelescope : Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (globalDiagram f) (globalTransition f)

/-- The unchanged restriction at each finite stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedTelescope.lean:47"
  "adaptation" "Original global supported telescope with unchanged stage and whole height"]
def finiteRestriction (i : ℕ) :
    globalDiagram f i ⟶ boundedAboveFlatCoefficientSupportedBassDiagram f i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor)

/-- Original seed compatibility gives the exact finite transition square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedTelescope.lean:53"
  "adaptation" "Original global supported telescope with unchanged stage and whole height"]
theorem finiteRestriction_transition (i : ℕ) :
    finiteRestriction f i ≫ boundedAboveFlatCoefficientSupportedBassTransition f i =
      globalTransition f i ≫ finiteRestriction f (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (supportedLaurentAction f).track.seed (boundedAboveFlatCoefficientSupportedBassSeed f)
    (Functor.whiskerRight (supportedRowRestriction f) prespectrumFunctor)
    (supportedRowRestriction_seed f) i).symm

/-- Actual restriction into the existing native supported telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedTelescope.lean:62"
  "adaptation" "Original global supported telescope with unchanged stage and whole height"]
def telescopeRestriction :
    globalTelescope f ⟶ boundedAboveFlatCoefficientSupportedBassTelescopeFunctor f :=
  Telescope.diagramMap (globalDiagram f) (boundedAboveFlatCoefficientSupportedBassDiagram f)
    (globalTransition f) (boundedAboveFlatCoefficientSupportedBassTransition f)
    (finiteRestriction f) (finiteRestriction_transition f)

/-- Every original telescope cylinder retains its stage and full height. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedTelescope.lean:69"
  "adaptation" "Original global supported telescope with unchanged stage and whole height"]
theorem telescopeRestriction_cylinder (a : Under R) (n i : ℕ) (s : unitInterval)
    (x : ((globalDiagram f i).obj a).space n) :
    ((telescopeRestriction f).app a).map n
      (Telescope.cylinder (fun j => (globalDiagram f j).obj a)
        (fun j => (globalTransition f j).app a) n i (s, x)) =
    Telescope.cylinder (fun j => (boundedAboveFlatCoefficientSupportedBassDiagram f j).obj a)
      (fun j => (boundedAboveFlatCoefficientSupportedBassTransition f j).app a) n i
      (s, ((finiteRestriction f i).app a).map n x) :=
  Telescope.diagramMap_cylinder _ _ _ _ _ _ a n i s x

/-- Original stage inclusions commute with this same telescope map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedTelescope.lean:80"
  "adaptation" "Original global supported telescope with unchanged stage and whole height"]
theorem telescopeRestriction_inclusion (i : ℕ) :
    Telescope.diagramInclusion (globalDiagram f) (globalTransition f) i ≫
      telescopeRestriction f =
    finiteRestriction f i ≫ boundedAboveFlatCoefficientSupportedBassTelescopeInclusion f i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

end SupportedTelescope
end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
