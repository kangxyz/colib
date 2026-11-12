/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedBassTower
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenBassStages
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportConeStable
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientBassTelescope
public import Colib.KTheory.Bass.ModelDiagramIterateCofiberPreservation
public import Colib.Topology.Prespectrum.TelescopeDiagramMap
public import Colib.Topology.Prespectrum.TelescopeConeDescentStable
/-! # Original ordinary supported Bass completion

The native ambient completion is reused. The original whole-null telescope retains independent
null time and height, and finite excision supplies its cone and cone-fiber stability.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- Original supported completion with its unchanged native finite stages and seeds. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTelescope.lean:35"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
def boundedAboveFlatCoefficientSupportedBassTelescopeFunctor : Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedAboveFlatCoefficientSupportedBassDiagram f)
    (boundedAboveFlatCoefficientSupportedBassTransition f)

/-- The original coefficient-natural supported-forget telescope map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTelescope.lean:46"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
def boundedAboveFlatCoefficientSupportedBassTelescopeForget :
    boundedAboveFlatCoefficientSupportedBassTelescopeFunctor f ⟶
      boundedAboveFlatCoefficientAmbientBassTelescopeFunctor Q :=
  Telescope.diagramMap (boundedAboveFlatCoefficientSupportedBassDiagram f)
    (boundedAboveFlatCoefficientAmbientBassDiagram Q)
      (boundedAboveFlatCoefficientSupportedBassTransition f)
    (boundedAboveFlatCoefficientAmbientBassTransition Q)
      (boundedAboveFlatCoefficientSupportedBassForget f)
    (boundedAboveFlatCoefficientSupportedBassForget_transition f)

/-- The original ambient-to-coarse telescope map with all original finite components. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTelescope.lean:55"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
def boundedAboveFlatCoefficientAmbientBassTelescopeOpen :
    boundedAboveFlatCoefficientAmbientBassTelescopeFunctor Q ⟶
      boundedAboveFlatCoefficientOpenBassTelescopeFunctor f :=
  Telescope.diagramMap (boundedAboveFlatCoefficientAmbientBassDiagram Q)
    (boundedAboveFlatCoefficientOpenBassDiagram f)
      (boundedAboveFlatCoefficientAmbientBassTransition Q)
    (boundedAboveFlatCoefficientOpenBassTransition f) (boundedAboveFlatCoefficientAmbientBassOpen f)
    (boundedAboveFlatCoefficientAmbientBassOpen_transition f)

/-- The original supported finite-stage inclusions into its completion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTelescope.lean:64"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
def boundedAboveFlatCoefficientSupportedBassTelescopeInclusion (i : ℕ) :
    boundedAboveFlatCoefficientSupportedBassDiagram f i ⟶
      boundedAboveFlatCoefficientSupportedBassTelescopeFunctor f :=
  Telescope.diagramInclusion (boundedAboveFlatCoefficientSupportedBassDiagram f)
    (boundedAboveFlatCoefficientSupportedBassTransition f) i

/-- The original supported-forget telescope map retains every unchanged inclusion face. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTelescope.lean:78"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
theorem boundedAboveFlatCoefficientSupportedBassTelescopeInclusion_forget (i : ℕ) :
    boundedAboveFlatCoefficientSupportedBassTelescopeInclusion f i ≫
        boundedAboveFlatCoefficientSupportedBassTelescopeForget f =
      boundedAboveFlatCoefficientSupportedBassForget f i ≫
        boundedAboveFlatCoefficientAmbientBassTelescopeInclusion Q i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- Original fine-to-coarse completion retains every unchanged ambient stage inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTelescope.lean:86"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
theorem boundedAboveFlatCoefficientAmbientBassTelescopeInclusion_open (i : ℕ) :
    boundedAboveFlatCoefficientAmbientBassTelescopeInclusion Q i ≫
        boundedAboveFlatCoefficientAmbientBassTelescopeOpen f =
      boundedAboveFlatCoefficientAmbientBassOpen f i ≫
        boundedAboveFlatCoefficientOpenBassTelescopeInclusion f i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- The same complete finite localization nulls define the original coefficient telescope null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTelescope.lean:94"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
def boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull :
    DiagramNullHomotopy (boundedAboveFlatCoefficientSupportedBassTelescopeForget f)
      (boundedAboveFlatCoefficientAmbientBassTelescopeOpen f) where
  homotopy a := Telescope.mapNullHomotopy
    (fun i ↦ (boundedAboveFlatCoefficientSupportedBassDiagram f i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedBassTransition f i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientAmbientBassDiagram Q i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientAmbientBassTransition Q i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientOpenBassTransition f i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedBassForget f i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientAmbientBassOpen f i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedAboveFlatCoefficientSupportedBassForget_transition
      f i))
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedAboveFlatCoefficientAmbientBassOpen_transition f i))
    (fun i ↦ (boundedAboveFlatCoefficientSupportedBassOpenNull f i).homotopy a)
    (fun i m s x ↦ boundedAboveFlatCoefficientSupportedBassOpenNull_transition f i a m s x)
  naturality {a b} g m s x := by
    induction x using Quot.inductionOn with
    | h z =>
      change Telescope.cylinder
          (fun i ↦ (boundedAboveFlatCoefficientOpenBassDiagram f i).obj b)
          (fun i ↦ (boundedAboveFlatCoefficientOpenBassTransition f i).app b) m z.1
          (z.2.1, ((boundedAboveFlatCoefficientOpenBassDiagram f z.1).map g).map m
            (((boundedAboveFlatCoefficientSupportedBassOpenNull f z.1).homotopy a).level m (s,
              z.2.2))) =
        Telescope.cylinder
          (fun i ↦ (boundedAboveFlatCoefficientOpenBassDiagram f i).obj b)
          (fun i ↦ (boundedAboveFlatCoefficientOpenBassTransition f i).app b) m z.1
          (z.2.1, ((boundedAboveFlatCoefficientSupportedBassOpenNull f z.1).homotopy b).level m
            (s, ((boundedAboveFlatCoefficientSupportedBassDiagram f z.1).map g).map m z.2.2))
      exact congrArg (fun y ↦ Telescope.cylinder
        (fun i ↦ (boundedAboveFlatCoefficientOpenBassDiagram f i).obj b)
        (fun i ↦ (boundedAboveFlatCoefficientOpenBassTransition f i).app b) m z.1 (z.2.1, y))
        ((boundedAboveFlatCoefficientSupportedBassOpenNull f z.1).naturality g m s z.2.2)

/-- The canonical null time and original telescope height stay independent. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTelescope.lean:129"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
theorem boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull_cylinder
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedBassDiagram f i).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a).level m
      (s, Telescope.cylinder (fun k ↦ (boundedAboveFlatCoefficientSupportedBassDiagram f k).obj a)
        (fun k ↦ (boundedAboveFlatCoefficientSupportedBassTransition f k).app a) m i (t, x)) =
    Telescope.cylinder (fun k ↦ (boundedAboveFlatCoefficientOpenBassDiagram f k).obj a)
      (fun k ↦ (boundedAboveFlatCoefficientOpenBassTransition f k).app a) m i
        (t, ((boundedAboveFlatCoefficientSupportedBassOpenNull f i).homotopy a).level m (s, x)) :=
          rfl

/-- The original supported telescope cone descends using precisely the same complete null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTelescope.lean:140"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
def boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap :
    mappingConeDiagram (boundedAboveFlatCoefficientSupportedBassTelescopeForget f) ⟶
      boundedAboveFlatCoefficientOpenBassTelescopeFunctor f :=
  mappingConeDescTransformation (boundedAboveFlatCoefficientSupportedBassTelescopeForget f)
    (boundedAboveFlatCoefficientAmbientBassTelescopeOpen f)
    (boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy
    (boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull f).naturality

/-- The original ambient inclusion face is exactly the original ambient-to-coarse completion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTelescope.lean:149"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
theorem boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap_inclusion (a : Under R) :
    mappingConeInclusion ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a) ≫
        (boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap f).app a =
      (boundedAboveFlatCoefficientAmbientBassTelescopeOpen f).app a := mappingConeInclusion_desc _
        _ _

/-- Actual finite Model excision supplies the original supported telescope cone-fiber comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTelescope.lean:155"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
theorem boundedAboveFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence
    (a : Under R) : IsStableEquivalence (mappingConeFiberComparison
      ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)) := by
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientSupportedBassDiagram f i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientSupportedModelFunctor f) a m
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientAmbientBassDiagram Q i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientSectionModelRow Q) a m
  exact Telescope.coneFiberComparison_isStableEquivalence
    (fun i ↦ (boundedAboveFlatCoefficientSupportedBassDiagram f i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedBassTransition f i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientAmbientBassDiagram Q i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientAmbientBassTransition Q i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedBassForget f i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedAboveFlatCoefficientSupportedBassForget_transition
      f i))
    (fun i ↦ boundedAboveFlatCoefficientSupportedBassForget_coneFiber_isStableEquivalence f i a)

/-- The original supported telescope cone descent is stable in every signed degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTelescope.lean:174"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
theorem boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap f).app a)
      := by
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientSupportedBassDiagram f i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientSupportedModelFunctor f) a m
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientAmbientBassDiagram Q i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientSectionModelRow Q) a m
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientOpenBassDiagram f i).obj a).space m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientOpenModelFunctor f) a m
  exact Telescope.coneDesc_isStableEquivalence
    (fun i ↦ (boundedAboveFlatCoefficientSupportedBassDiagram f i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedBassTransition f i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientAmbientBassDiagram Q i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientAmbientBassTransition Q i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientOpenBassDiagram f i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientOpenBassTransition f i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedBassForget f i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientAmbientBassOpen f i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedAboveFlatCoefficientSupportedBassForget_transition
      f i))
    (fun i ↦ congrArg (fun η ↦ η.app a) (boundedAboveFlatCoefficientAmbientBassOpen_transition f i))
    (fun i ↦ (boundedAboveFlatCoefficientSupportedBassOpenNull f i).homotopy a)
    (fun i m s x ↦ boundedAboveFlatCoefficientSupportedBassOpenNull_transition f i a m s x)
    (fun i ↦ boundedAboveFlatCoefficientSupportedBassOpenConeMap_isStableEquivalence f i a)

/-- The actual signed coarse boundary uses the original inclusion and this same whole null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedBassTelescope.lean:202"
  "adaptation" "Original finite supported Bass tower and whole-null cone stability"]
theorem boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap_connecting
    (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        ((boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap f).app a) ≫
      stableFiberConnecting ((boundedAboveFlatCoefficientAmbientBassTelescopeOpen f).app a) d =
    stableMappingConeConnecting ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
      (boundedAboveFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a)
        d ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift
          ((boundedAboveFlatCoefficientAmbientBassTelescopeOpen f).app a)
          ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
          ((boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a)) :=
  mappingConeDesc_connecting _ _ _
    (boundedAboveFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a) d

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0593"]
  boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap_isStableEquivalence

attribute [colib_tag "COL-0593"]
  boundedAboveFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence

attribute [colib_tag "COL-0593"]
  boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap_connecting

end AlgebraicGeometry.Scheme.Modules
