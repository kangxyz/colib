/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFiberBassTower
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenBassTelescopes
public import Colib.Topology.Prespectrum.TelescopeConeDescentStable


/-!
# Original auxiliary intersection-support telescope cone and coarse completion

Original fiber and auxiliary ambient finite stages and seeds define the literal
native telescopes. Their unchanged inclusion and identity weakness change carry
the whole null from the same finite supported localization nulls. Genuine finite
Model excision and cone stability pass to this original telescope cone. Null
time and telescope height remain independent on every original cylinder.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory Topology AlgebraicGeometry Topology.LoopPrespectrum
open KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Original supported completion with its unchanged native finite stages and seeds. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTelescope.lean:34"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
def boundedAboveFlatCoefficientSupportedFiberBassTelescopeFunctor : Under R ⥤
  LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedAboveFlatCoefficientSupportedFiberBassDiagram f T)
    (boundedAboveFlatCoefficientSupportedFiberBassTransition f T)

/-- Original native fine ambient completion with its unchanged finite stages and seeds. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTelescope.lean:39"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
def boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFunctor :
    Under R ⥤ LoopPrespectrum.{u+1} :=
  Telescope.diagramFunctor (boundedAboveFlatCoefficientSupportedAmbientBassDiagram T)
    (boundedAboveFlatCoefficientSupportedAmbientBassTransition T)

/-- The original coefficient-natural supported-forget telescope map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTelescope.lean:45"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
def boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget :
    boundedAboveFlatCoefficientSupportedFiberBassTelescopeFunctor f T ⟶
      boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFunctor T :=
  Telescope.diagramMap (boundedAboveFlatCoefficientSupportedFiberBassDiagram f T)
    (boundedAboveFlatCoefficientSupportedAmbientBassDiagram T)
      (boundedAboveFlatCoefficientSupportedFiberBassTransition f T)
    (boundedAboveFlatCoefficientSupportedAmbientBassTransition T)
      (boundedAboveFlatCoefficientSupportedFiberBassForget f T)
    (boundedAboveFlatCoefficientSupportedFiberBassForget_transition f T)

/-- The original ambient-to-coarse telescope map with all original finite components. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTelescope.lean:56"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
def boundedAboveFlatCoefficientSupportedAmbientBassTelescopeOpen :
    boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFunctor T ⟶
      boundedAboveFlatCoefficientSupportedOpenBassTelescopeFunctor f T :=
  Telescope.diagramMap (boundedAboveFlatCoefficientSupportedAmbientBassDiagram T)
    (boundedAboveFlatCoefficientSupportedOpenBassDiagram f T)
      (boundedAboveFlatCoefficientSupportedAmbientBassTransition T)
    (boundedAboveFlatCoefficientSupportedOpenBassTransition f T)
      (boundedAboveFlatCoefficientSupportedAmbientBassOpen f T)
    (boundedAboveFlatCoefficientSupportedAmbientBassOpen_transition f T)

/-- The original supported finite-stage inclusions into its completion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTelescope.lean:67"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
def boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion (i : ℕ) :
    boundedAboveFlatCoefficientSupportedFiberBassDiagram f T i ⟶
      boundedAboveFlatCoefficientSupportedFiberBassTelescopeFunctor f T :=
  Telescope.diagramInclusion (boundedAboveFlatCoefficientSupportedFiberBassDiagram f T)
    (boundedAboveFlatCoefficientSupportedFiberBassTransition f T) i

/-- The original ambient finite-stage inclusions into its completion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTelescope.lean:74"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
def boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion (i : ℕ) :
    boundedAboveFlatCoefficientSupportedAmbientBassDiagram T i ⟶
      boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFunctor T :=
  Telescope.diagramInclusion (boundedAboveFlatCoefficientSupportedAmbientBassDiagram T)
    (boundedAboveFlatCoefficientSupportedAmbientBassTransition T) i

/-- The original supported-forget telescope map retains every unchanged inclusion face. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTelescope.lean:81"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
theorem boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion_forget (i : ℕ) :
    boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion f T i ≫
        boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T =
      boundedAboveFlatCoefficientSupportedFiberBassForget f T i ≫
        boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

omit [IsOpenImmersion f.left] in
/-- Original fine-to-coarse completion retains every unchanged ambient stage inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTelescope.lean:90"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
theorem boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion_open (i : ℕ) :
    boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T i ≫
        boundedAboveFlatCoefficientSupportedAmbientBassTelescopeOpen f T =
      boundedAboveFlatCoefficientSupportedAmbientBassOpen f T i ≫
        boundedAboveFlatCoefficientSupportedOpenBassTelescopeInclusion f T i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- The same complete finite localization nulls define the original coefficient telescope null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTelescope.lean:98"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
def boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull :
    DiagramNullHomotopy (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T)
      (boundedAboveFlatCoefficientSupportedAmbientBassTelescopeOpen f T) where
  homotopy a := Telescope.mapNullHomotopy
    (fun i ↦ (boundedAboveFlatCoefficientSupportedFiberBassDiagram f T i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedFiberBassTransition f T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedAmbientBassDiagram T i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedAmbientBassTransition T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassTransition f T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedFiberBassForget f T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedAmbientBassOpen f T i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a)
      (boundedAboveFlatCoefficientSupportedFiberBassForget_transition f
      T i))
    (fun i ↦ congrArg (fun η ↦ η.app a)
      (boundedAboveFlatCoefficientSupportedAmbientBassOpen_transition f
      T i))
    (fun i ↦ (boundedAboveFlatCoefficientSupportedFiberBassOpenNull f T i).homotopy a)
    (fun i m s x ↦ boundedAboveFlatCoefficientSupportedFiberBassOpenNull_transition f T i a m s x)
  naturality {a b} g m s x := by
    induction x using Quot.inductionOn with
    | h z =>
      change Telescope.cylinder
          (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i).obj b)
          (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassTransition f T i).app b) m z.1
          (z.2.1, ((boundedAboveFlatCoefficientSupportedOpenBassDiagram f T z.1).map g).map m
            (((boundedAboveFlatCoefficientSupportedFiberBassOpenNull f T z.1).homotopy a).level m
              (s,
              z.2.2))) =
        Telescope.cylinder
          (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i).obj b)
          (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassTransition f T i).app b) m z.1
          (z.2.1, ((boundedAboveFlatCoefficientSupportedFiberBassOpenNull f T z.1).homotopy
            b).level m
            (s, ((boundedAboveFlatCoefficientSupportedFiberBassDiagram f T z.1).map g).map m z.2.2))
      exact congrArg (fun y ↦ Telescope.cylinder
        (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i).obj b)
        (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassTransition f T i).app b) m z.1
          (z.2.1, y))
        ((boundedAboveFlatCoefficientSupportedFiberBassOpenNull f T z.1).naturality g m s z.2.2)

/-- The canonical null time and original telescope height stay independent. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTelescope.lean:136"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
theorem boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull_cylinder
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedFiberBassDiagram f T i).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy a).level m
      (s, Telescope.cylinder (fun k ↦ (boundedAboveFlatCoefficientSupportedFiberBassDiagram f T
        k).obj a)
        (fun k ↦ (boundedAboveFlatCoefficientSupportedFiberBassTransition f T k).app a) m i (t,
          x)) =
    Telescope.cylinder (fun k ↦ (boundedAboveFlatCoefficientSupportedOpenBassDiagram f T k).obj a)
      (fun k ↦ (boundedAboveFlatCoefficientSupportedOpenBassTransition f T k).app a) m i
        (t, ((boundedAboveFlatCoefficientSupportedFiberBassOpenNull f T i).homotopy a).level m (s,
          x)) :=
          rfl

/-- The original supported telescope cone descends using precisely the same complete null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTelescope.lean:148"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
def boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap :
    mappingConeDiagram (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T) ⟶
      boundedAboveFlatCoefficientSupportedOpenBassTelescopeFunctor f T :=
  mappingConeDescTransformation (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T)
    (boundedAboveFlatCoefficientSupportedAmbientBassTelescopeOpen f T)
    (boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy
    (boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).naturality

/-- The original ambient inclusion face is exactly the original ambient-to-coarse completion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTelescope.lean:157"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
theorem boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap_inclusion (a : Under R) :
    mappingConeInclusion ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app
      a) ≫
        (boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap f T).app a =
      (boundedAboveFlatCoefficientSupportedAmbientBassTelescopeOpen f T).app a :=
        mappingConeInclusion_desc _ _ _

/-- Actual finite Model excision supplies the original supported telescope cone-fiber comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTelescope.lean:164"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
theorem boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget_coneFiber_isStableEquivalence
    (a : Under R) : IsStableEquivalence (mappingConeFiberComparison
      ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)) := by
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientSupportedFiberBassDiagram f T i).obj a).space
    m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T) a m
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientSupportedAmbientBassDiagram T i).obj a).space
    m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T) a m
  exact Telescope.coneFiberComparison_isStableEquivalence
    (fun i ↦ (boundedAboveFlatCoefficientSupportedFiberBassDiagram f T i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedFiberBassTransition f T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedAmbientBassDiagram T i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedAmbientBassTransition T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedFiberBassForget f T i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a)
      (boundedAboveFlatCoefficientSupportedFiberBassForget_transition f
      T i))
    (fun i ↦ boundedAboveFlatCoefficientSupportedFiberBassForget_coneFiber_isStableEquivalence f T
      i a)

/-- The original supported telescope cone descent is stable in every signed degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTelescope.lean:184"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
theorem boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap f
      T).app a)
      := by
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientSupportedFiberBassDiagram f T i).obj a).space
    m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T) a m
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientSupportedAmbientBassDiagram T i).obj a).space
    m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T) a m
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i).obj a).space
    m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientSupportedOpenModelFunctor f T) a m
  exact Telescope.coneDesc_isStableEquivalence
    (fun i ↦ (boundedAboveFlatCoefficientSupportedFiberBassDiagram f T i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedFiberBassTransition f T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedAmbientBassDiagram T i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedAmbientBassTransition T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassTransition f T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedFiberBassForget f T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedAmbientBassOpen f T i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a)
      (boundedAboveFlatCoefficientSupportedFiberBassForget_transition f
      T i))
    (fun i ↦ congrArg (fun η ↦ η.app a)
      (boundedAboveFlatCoefficientSupportedAmbientBassOpen_transition f
      T i))
    (fun i ↦ (boundedAboveFlatCoefficientSupportedFiberBassOpenNull f T i).homotopy a)
    (fun i m s x ↦ boundedAboveFlatCoefficientSupportedFiberBassOpenNull_transition f T i a m s x)
    (fun i ↦ boundedAboveFlatCoefficientSupportedFiberBassOpenConeMap_isStableEquivalence f T i a)

/-- The actual signed coarse boundary uses the original inclusion and this same whole null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedFiberBassTelescope.lean:215"
  "adaptation" "Actual auxiliary fiber telescope, original whole null and signed coarse completion"]
theorem boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap_connecting
    (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap f T).app a) ≫
      stableFiberConnecting ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeOpen f
        T).app a) d
        =
    stableMappingConeConnecting ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f
      T).app
      a)
      (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget_coneFiber_isStableEquivalence
        f T a)
        d ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift
          ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeOpen f T).app a)
          ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
          ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy a)) :=
  mappingConeDesc_connecting _ _ _
    (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget_coneFiber_isStableEquivalence f
      T a) d


end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0588"]
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull_cylinder

attribute [colib_tag "COL-0588"]
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap_isStableEquivalence

attribute [colib_tag "COL-0588"]
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap_connecting

end AlgebraicGeometry.Scheme.Modules
