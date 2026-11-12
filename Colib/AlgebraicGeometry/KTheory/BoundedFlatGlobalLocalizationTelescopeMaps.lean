/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalOpenTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedForgetSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalOpenChangeSeed
/-! # Actual original global localization telescope arrows and comparison squares -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.LocalizationTelescope
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The actual supported inclusion at each original finite stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationTelescopeMaps.lean:28"
  "adaptation" "Original global localization arrows and whole-height strict comparison squares"]
def finiteForget (i : ℕ) :
    SupportedTelescope.globalDiagram f i ⟶ globalDiagram Q i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (Functor.whiskerRight (supportedRowForget f) prespectrumFunctor)

/-- The actual fine-to-coarse identity at each original finite stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationTelescopeMaps.lean:34"
  "adaptation" "Original global localization arrows and whole-height strict comparison squares"]
def finiteOpen (i : ℕ) :
    globalDiagram Q i ⟶ OpenTelescope.globalDiagram f i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (Functor.whiskerRight (openRowChangeWeak f) prespectrumFunctor)

/-- The original supported seed gives the finite inclusion transition square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationTelescopeMaps.lean:40"
  "adaptation" "Original global localization arrows and whole-height strict comparison squares"]
theorem finiteForget_transition (i : ℕ) :
    finiteForget f i ≫ globalTransition Q i =
      SupportedTelescope.globalTransition f i ≫ finiteForget f (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (supportedLaurentAction f).track.seed (globalLaurentAction Q).track.seed
    (Functor.whiskerRight (supportedRowForget f) prespectrumFunctor)
    (supportedRowForget_seed f) i).symm

/-- The same global unit gives the finite change-of-weakness transition square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationTelescopeMaps.lean:49"
  "adaptation" "Original global localization arrows and whole-height strict comparison squares"]
theorem finiteOpen_transition (i : ℕ) :
    finiteOpen f i ≫ OpenTelescope.globalTransition f i =
      globalTransition Q i ≫ finiteOpen f (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (globalLaurentAction Q).track.seed (openLaurentAction f).track.seed
    (Functor.whiskerRight (openRowChangeWeak f) prespectrumFunctor)
    (openRowChangeWeak_seed f) i).symm

/-- The actual global supported-to-ambient telescope arrow. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationTelescopeMaps.lean:58"
  "adaptation" "Original global localization arrows and whole-height strict comparison squares"]
def forget : SupportedTelescope.globalTelescope f ⟶ globalTelescope Q :=
  Telescope.diagramMap (SupportedTelescope.globalDiagram f) (globalDiagram Q)
    (SupportedTelescope.globalTransition f) (globalTransition Q)
    (finiteForget f) (finiteForget_transition f)

/-- The actual global ambient-to-coarse telescope arrow. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationTelescopeMaps.lean:64"
  "adaptation" "Original global localization arrows and whole-height strict comparison squares"]
def openMap : globalTelescope Q ⟶ OpenTelescope.globalTelescope f :=
  Telescope.diagramMap (globalDiagram Q) (OpenTelescope.globalDiagram f)
    (globalTransition Q) (OpenTelescope.globalTransition f)
    (finiteOpen f) (finiteOpen_transition f)

/-- Forgetting support preserves every stage and independent telescope height. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationTelescopeMaps.lean:70"
  "adaptation" "Original global localization arrows and whole-height strict comparison squares"]
theorem forget_cylinder (a : Under R) (n i : ℕ) (t : unitInterval)
    (x : ((SupportedTelescope.globalDiagram f i).obj a).space n) :
    ((forget f).app a).map n
      (Telescope.cylinder (fun j => (SupportedTelescope.globalDiagram f j).obj a)
        (fun j => (SupportedTelescope.globalTransition f j).app a) n i (t, x)) =
    Telescope.cylinder (fun j => (globalDiagram Q j).obj a)
      (fun j => (globalTransition Q j).app a) n i
      (t, ((finiteForget f i).app a).map n x) :=
  Telescope.diagramMap_cylinder _ _ _ _ _ _ a n i t x

/-- Changing weakness preserves every stage and independent telescope height. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationTelescopeMaps.lean:81"
  "adaptation" "Original global localization arrows and whole-height strict comparison squares"]
theorem openMap_cylinder (a : Under R) (n i : ℕ) (t : unitInterval)
    (x : ((globalDiagram Q i).obj a).space n) :
    ((openMap f).app a).map n
      (Telescope.cylinder (fun j => (globalDiagram Q j).obj a)
        (fun j => (globalTransition Q j).app a) n i (t, x)) =
    Telescope.cylinder (fun j => (OpenTelescope.globalDiagram f j).obj a)
      (fun j => (OpenTelescope.globalTransition f j).app a) n i
      (t, ((finiteOpen f i).app a).map n x) :=
  Telescope.diagramMap_cylinder _ _ _ _ _ _ a n i t x

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.LocalizationTelescope

