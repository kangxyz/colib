/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterCoefficientSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryIteratedNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFiberBassTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedGradedBassTelescope
public import Colib.KTheory.Bass.StrictDiagramIndexRowMapTelescopeNaturality
public import Colib.KTheory.Bass.ModelDiagramConnectivity


/-! # Actual auxiliary-support Spec comparisons of the original iterated telescopes -/
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
namespace AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection GeometricSeedCospan ParameterLaurentTrack
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]
    (T : Q.left.Opens)

/-- The actual fiber Spec comparison descends using its proved original seed square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterTelescopeComparison.lean:33"
  "adaptation" "Original auxiliary actual Spec comparisons and the unchanged selected whole null"]
def fiberTelescopeComparison :
    specUnder ⋙
      SchemeNaturalSeed.iteratedTelescope (ParameterAuxiliarySupport.fiberAction f.left T) ⟶
      boundedAboveFlatCoefficientSupportedFiberBassTelescopeFunctor f T :=
  StrictDiagramIndexRowMap.telescopeMap specUnder (laurentUnderSquareFunctor _)
    squareFunctor specSquare (F := ParameterAuxiliarySupport.fiber f.left T ⋙ prespectrumFunctor)
    (G := boundedAboveFlatCoefficientSupportedFiberModelFunctor f T ⋙ prespectrumFunctor)
    (Functor.whiskerRight (fiberComparison f T) prespectrumFunctor)
    (SchemeNaturalSeed.seed (ParameterAuxiliarySupport.fiberAction f.left T))
    (boundedAboveFlatCoefficientSupportedFiberLaurentAction f T).track.seed (by
      simpa only [rowBassComparison, Category.assoc] using fiber_seed_square f T)

/-- The complete fiber comparison preserves the original cylinder height and stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterTelescopeComparison.lean:46"
  "adaptation" "Original auxiliary actual Spec comparisons and the unchanged selected whole null"]
theorem fiberTelescopeComparison_cylinder
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n i : ℕ) (s : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (ParameterAuxiliarySupport.fiber f.left T ⋙ prespectrumFunctor)).obj
        (specUnder.obj a)).space n) :
    ((fiberTelescopeComparison f T).app a).map n
      (Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj
        (ParameterAuxiliarySupport.fiber f.left T ⋙ prespectrumFunctor)).obj (specUnder.obj a))
        (fun j => (strictDiagramTransition squareFunctor
          (SchemeNaturalSeed.seed (ParameterAuxiliarySupport.fiberAction f.left T)) j).app
            (specUnder.obj a)) n i (s, x)) =
    Telescope.cylinder (fun j => ((strictDiagramIterate (laurentUnderSquareFunctor _) j).obj
      (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T ⋙ prespectrumFunctor)).obj a)
      (fun j => (strictDiagramTransition (laurentUnderSquareFunctor _)
        (boundedAboveFlatCoefficientSupportedFiberLaurentAction f T).track.seed j).app a) n i
      (s, ((fiberFiniteComparison f T i).app a).map n x) := rfl

/-- The actual fiber comparison is stable by its three-model finite comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterTelescopeComparison.lean:64"
  "adaptation" "Original auxiliary actual Spec comparisons and the unchanged selected whole null"]
theorem fiberTelescopeComparison_stable
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((fiberTelescopeComparison f T).app a) := by
  apply StrictDiagramIndexRowMap.telescopeMap_stable
  exact fun i => fiberFiniteComparison_stable f T i a

/-- The actual ambient Spec comparison descends using its proved original seed square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterTelescopeComparison.lean:71"
  "adaptation" "Original auxiliary actual Spec comparisons and the unchanged selected whole null"]
def ambientTelescopeComparison (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens) :
    specUnder ⋙
      SchemeNaturalSeed.iteratedTelescope (ParameterAuxiliarySupport.ambientAction T) ⟶
      boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFunctor (Q := Q) T :=
  StrictDiagramIndexRowMap.telescopeMap specUnder (laurentUnderSquareFunctor _)
    squareFunctor specSquare (F := ParameterAuxiliarySupport.ambient T ⋙ prespectrumFunctor)
    (G := boundedAboveFlatCoefficientSupportedAmbientModelFunctor T ⋙ prespectrumFunctor)
    (Functor.whiskerRight (ambientComparison Q T) prespectrumFunctor)
    (SchemeNaturalSeed.seed (ParameterAuxiliarySupport.ambientAction T))
    (boundedAboveFlatCoefficientSupportedAmbientLaurentAction (Q := Q) T).track.seed (by
      simpa only [rowBassComparison, Category.assoc] using ambient_seed_square Q T)

/-- The complete ambient comparison preserves the original cylinder height and stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterTelescopeComparison.lean:85"
  "adaptation" "Original auxiliary actual Spec comparisons and the unchanged selected whole null"]
theorem ambientTelescopeComparison_cylinder (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n i : ℕ) (s : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (ParameterAuxiliarySupport.ambient T ⋙ prespectrumFunctor)).obj
        (specUnder.obj a)).space n) :
    ((ambientTelescopeComparison Q T).app a).map n
      (Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj
        (ParameterAuxiliarySupport.ambient T ⋙ prespectrumFunctor)).obj (specUnder.obj a))
        (fun j => (strictDiagramTransition squareFunctor
          (SchemeNaturalSeed.seed (ParameterAuxiliarySupport.ambientAction T)) j).app
            (specUnder.obj a)) n i (s, x)) =
    Telescope.cylinder (fun j => ((strictDiagramIterate (laurentUnderSquareFunctor _) j).obj
      (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T ⋙ prespectrumFunctor)).obj a)
      (fun j => (strictDiagramTransition (laurentUnderSquareFunctor _)
        (boundedAboveFlatCoefficientSupportedAmbientLaurentAction (Q := Q) T).track.seed j).app a)
          n i
      (s, ((ambientFiniteComparison Q T i).app a).map n x) := rfl

/-- The actual ambient comparison is stable by its three-model finite comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterTelescopeComparison.lean:104"
  "adaptation" "Original auxiliary actual Spec comparisons and the unchanged selected whole null"]
theorem ambientTelescopeComparison_stable (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((ambientTelescopeComparison Q T).app a) := by
  apply StrictDiagramIndexRowMap.telescopeMap_stable
  exact fun i => ambientFiniteComparison_stable Q T i a

/-- The actual open Spec comparison descends using its proved original seed square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterTelescopeComparison.lean:112"
  "adaptation" "Original auxiliary actual Spec comparisons and the unchanged selected whole null"]
def openTelescopeComparison :
    specUnder ⋙
      SchemeNaturalSeed.iteratedTelescope (ParameterAuxiliarySupport.openAction f.left T) ⟶
      boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T :=
  StrictDiagramIndexRowMap.telescopeMap specUnder (laurentUnderSquareFunctor _)
    squareFunctor specSquare
    (F := ParameterAuxiliarySupport.openModel f.left T ⋙ prespectrumFunctor)
    (G := boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T ⋙ prespectrumFunctor)
    (Functor.whiskerRight (openComparison f T) prespectrumFunctor)
    (SchemeNaturalSeed.seed (ParameterAuxiliarySupport.openAction f.left T))
    (boundedAboveFlatCoefficientSupportedFullOpenLaurentAction f T).track.seed (by
      simpa only [rowBassComparison, Category.assoc] using open_seed_square f T)

omit [IsOpenImmersion f.left] in
/-- The complete open comparison preserves the original cylinder height and stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterTelescopeComparison.lean:127"
  "adaptation" "Original auxiliary actual Spec comparisons and the unchanged selected whole null"]
theorem openTelescopeComparison_cylinder
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n i : ℕ) (s : unitInterval)
    (x : (((strictDiagramIterate squareFunctor i).obj
      (ParameterAuxiliarySupport.openModel f.left T ⋙ prespectrumFunctor)).obj
        (specUnder.obj a)).space n) :
    ((openTelescopeComparison f T).app a).map n
      (Telescope.cylinder (fun j => ((strictDiagramIterate squareFunctor j).obj
        (ParameterAuxiliarySupport.openModel f.left T ⋙ prespectrumFunctor)).obj (specUnder.obj a))
        (fun j => (strictDiagramTransition squareFunctor
          (SchemeNaturalSeed.seed (ParameterAuxiliarySupport.openAction f.left T)) j).app
            (specUnder.obj a)) n i (s, x)) =
    Telescope.cylinder (fun j => ((strictDiagramIterate (laurentUnderSquareFunctor _) j).obj
      (boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T ⋙ prespectrumFunctor)).obj a)
      (fun j => (strictDiagramTransition (laurentUnderSquareFunctor _)
        (boundedAboveFlatCoefficientSupportedFullOpenLaurentAction f T).track.seed j).app a) n i
      (s, ((openFiniteComparison f T i).app a).map n x) := rfl

omit [IsOpenImmersion f.left] in
/-- The actual open comparison is stable by its three-model finite comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterTelescopeComparison.lean:146"
  "adaptation" "Original auxiliary actual Spec comparisons and the unchanged selected whole null"]
theorem openTelescopeComparison_stable
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((openTelescopeComparison f T).app a) := by
  apply StrictDiagramIndexRowMap.telescopeMap_stable
  exact fun i => openFiniteComparison_stable f T i a

end AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient


namespace AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient

attribute [colib_tag "COL-0591"]
  fiberTelescopeComparison_stable

attribute [colib_tag "COL-0591"]
  ambientTelescopeComparison_stable

attribute [colib_tag "COL-0591"]
  openTelescopeComparison_stable

end AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
