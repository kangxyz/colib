/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenBassTelescopes
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedGradedBassTower
public import Colib.Topology.Prespectrum.TelescopeDiagramMap
public import Colib.Topology.Prespectrum.TelescopeConeDescentStable
public import Colib.Topology.Prespectrum.TelescopeStableRepresentability
public import Colib.Topology.Prespectrum.ConeStableVanishing


/-!
# Original auxiliary-supported C_Z/F_Z/G_Z completion and actual stable restriction

The original finite stages and transitions determine the actual coefficient
telescopes and unchanged r-infinity/q-infinity maps. Whole finite localization
null transition equations construct the same complete telescope null, with
localization-null time and telescope height independent.

Actual finite Model cone descent and excision pass to this original telescope
cone. The constructed graded transition nulls kill all signed telescope classes
via finite representatives. Its unchanged cone therefore vanishes, proving the
actual coarse-to-fine restriction stable in every integer degree. No uniform
whole-telescope connectivity or classical K-theory comparison is assumed.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Original coefficient-natural r-infinity retaining all finite restriction components. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:52"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
def boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction :
    boundedAboveFlatCoefficientSupportedOpenBassTelescopeFunctor f T ⟶
      boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T :=
  Telescope.diagramMap (boundedAboveFlatCoefficientSupportedOpenBassDiagram f T)
    (boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T)
      (boundedAboveFlatCoefficientSupportedOpenBassTransition f T)
    (boundedAboveFlatCoefficientSupportedFullOpenBassTransition f T)
      (boundedAboveFlatCoefficientSupportedOpenBassRestriction f T)
    (boundedAboveFlatCoefficientSupportedOpenBassRestriction_transition f T)

omit [IsOpenImmersion f.left] in
/-- The original restriction retains every finite inclusion face. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:78"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem boundedAboveFlatCoefficientSupportedOpenBassTelescopeInclusion_restriction (i : ℕ) :
    boundedAboveFlatCoefficientSupportedOpenBassTelescopeInclusion f T i ≫
        boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T =
      boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i ≫
        boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- Original G completion with the exact original graded seeds and transitions. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:88"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
def boundedAboveFlatCoefficientSupportedGradedOpenBassTelescopeFunctor : Under R ⥤
  LoopPrespectrum.{u+1}
  :=
  Telescope.diagramFunctor (boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T)
    (boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T)

/-- Original coefficient-natural q-infinity retaining all finite grading components. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:94"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
def boundedAboveFlatCoefficientSupportedOpenBassTelescopeGrading :
    boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T ⟶
      boundedAboveFlatCoefficientSupportedGradedOpenBassTelescopeFunctor f T :=
  Telescope.diagramMap (boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T)
    (boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T)
      (boundedAboveFlatCoefficientSupportedFullOpenBassTransition f T)
    (boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T)
      (boundedAboveFlatCoefficientSupportedOpenBassGrading f T)
    (boundedAboveFlatCoefficientSupportedOpenBassGrading_transition f T)

/-- Original G stage inclusions with their unchanged initial cylinder faces. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:105"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
def boundedAboveFlatCoefficientSupportedGradedOpenBassTelescopeInclusion (i : ℕ) :
    boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T i ⟶
      boundedAboveFlatCoefficientSupportedGradedOpenBassTelescopeFunctor f T :=
  Telescope.diagramInclusion (boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T)
    (boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T) i

/-- The original grading retains every finite inclusion face. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:112"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem boundedAboveFlatCoefficientSupportedOpenBassTelescopeInclusion_grading (i : ℕ) :
    boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T i ≫
        boundedAboveFlatCoefficientSupportedOpenBassTelescopeGrading f T =
      boundedAboveFlatCoefficientSupportedOpenBassGrading f T i ≫
        boundedAboveFlatCoefficientSupportedGradedOpenBassTelescopeInclusion f T i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- The same complete finite localization nulls define the original coefficient telescope null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:120"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
def boundedAboveFlatCoefficientSupportedOpenBassTelescopeGradingNull :
    DiagramNullHomotopy (boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T)
      (boundedAboveFlatCoefficientSupportedOpenBassTelescopeGrading f T) where
  homotopy a := Telescope.mapNullHomotopy
    (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassTransition f T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedFullOpenBassTransition f T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassGrading f T i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a)
      (boundedAboveFlatCoefficientSupportedOpenBassRestriction_transition f T i))
    (fun i ↦ congrArg (fun η ↦ η.app a)
      (boundedAboveFlatCoefficientSupportedOpenBassGrading_transition f
      T i))
    (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassGradingNull f T i).homotopy a)
    (fun i m s x ↦ boundedAboveFlatCoefficientSupportedOpenBassGradingNull_transition f T i a m s x)
  naturality {a b} g m s x := by
    induction x using Quot.inductionOn with
    | h z =>
      change Telescope.cylinder
          (fun i ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T i).obj b)
          (fun i ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T i).app b) m z.1
          (z.2.1, ((boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T z.1).map g).map m
            (((boundedAboveFlatCoefficientSupportedOpenBassGradingNull f T z.1).homotopy a).level
              m (s,
              z.2.2))) =
        Telescope.cylinder
          (fun i ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T i).obj b)
          (fun i ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T i).app b) m z.1
          (z.2.1, ((boundedAboveFlatCoefficientSupportedOpenBassGradingNull f T z.1).homotopy
            b).level m
            (s, ((boundedAboveFlatCoefficientSupportedOpenBassDiagram f T z.1).map g).map m z.2.2))
      exact congrArg (fun y ↦ Telescope.cylinder
        (fun i ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T i).obj b)
        (fun i ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T i).app b) m z.1
          (z.2.1, y))
        ((boundedAboveFlatCoefficientSupportedOpenBassGradingNull f T z.1).naturality g m s z.2.2)

/-- The canonical null time and original telescope height stay independent. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:159"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem boundedAboveFlatCoefficientSupportedOpenBassTelescopeGradingNull_cylinder
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeGradingNull f T).homotopy a).level m
      (s, Telescope.cylinder (fun k ↦ (boundedAboveFlatCoefficientSupportedOpenBassDiagram f T
        k).obj a)
        (fun k ↦ (boundedAboveFlatCoefficientSupportedOpenBassTransition f T k).app a) m i (t, x)) =
    Telescope.cylinder (fun k ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T
      k).obj a)
      (fun k ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T k).app a) m i
        (t, ((boundedAboveFlatCoefficientSupportedOpenBassGradingNull f T i).homotopy a).level m
          (s, x))
          := rfl

/-- Actual whole transition nulls kill every original G stage-inclusion stable map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:171"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem boundedAboveFlatCoefficientSupportedGradedOpenBassTelescopeInclusion_stableMap_eq_zero
    (i : ℕ) (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientSupportedGradedOpenBassTelescopeInclusion f T i).app a) = 0 := by
  let E := fun k ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T k).obj a
  let τ := fun k ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T k).app a
  change (stableHomotopyFunctor d).map (Telescope.inclusion E τ i) = 0
  have hi := Telescope.inclusion_transition_stableMap E τ (Nat.le_succ i) d
  rw [Telescope.transition_succ] at hi
  have hz : (stableHomotopyFunctor d).map (τ i) = 0 :=
    boundedAboveFlatCoefficientSupportedGradedOpenBassTransition_stableMap_eq_zero f T i a d
  exact hi.trans (by rw [hz, CategoryTheory.Limits.zero_comp])

/-- Finite original stable representatives prove G-infinity vanishes in every integer degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:185"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem boundedAboveFlatCoefficientSupportedGradedOpenBassTelescope_stableClass_eq_zero
    (a : Under R) (d : ℤ)
    (x : stableHomotopyGroup ((boundedAboveFlatCoefficientSupportedGradedOpenBassTelescopeFunctor f
      T).obj a) d) :
    x = 0 := by
  let E := fun k ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T k).obj a
  let τ := fun k ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T k).app a
  let : ∀ i n, T1Space ((E i).space n) :=
    fun i n ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientSupportedGradedOpenModelFunctor f T) a n
  obtain ⟨i, y, hy⟩ := Telescope.exists_stable_representative E τ d x
  have hi :=
    boundedAboveFlatCoefficientSupportedGradedOpenBassTelescopeInclusion_stableMap_eq_zero f T i
    a d
  exact hy.symm.trans ((ConcreteCategory.congr_hom hi y).trans rfl)

/-- The actual signed G-infinity groups are subsingletons. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:201"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem boundedAboveFlatCoefficientSupportedGradedOpenBassTelescope_stableGroup_subsingleton
    (a : Under R) (d : ℤ) : Subsingleton (stableHomotopyGroup
      ((boundedAboveFlatCoefficientSupportedGradedOpenBassTelescopeFunctor f T).obj a) d) :=
  ⟨fun x y ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassTelescope_stableClass_eq_zero f T
    a d
    x).trans
    (boundedAboveFlatCoefficientSupportedGradedOpenBassTelescope_stableClass_eq_zero f T a d
      y).symm⟩

/-- The original telescope cone descends with precisely the same complete N-infinity. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:209"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
def boundedAboveFlatCoefficientSupportedOpenBassTelescopeConeComparison :
    mappingConeDiagram (boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T) ⟶
      boundedAboveFlatCoefficientSupportedGradedOpenBassTelescopeFunctor f T :=
  mappingConeDescTransformation (boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction
    f T)
    (boundedAboveFlatCoefficientSupportedOpenBassTelescopeGrading f T)
    (boundedAboveFlatCoefficientSupportedOpenBassTelescopeGradingNull f T).homotopy
    (boundedAboveFlatCoefficientSupportedOpenBassTelescopeGradingNull f T).naturality

/-- The original telescope cone inclusion has exactly q-infinity as its face. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:218"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem boundedAboveFlatCoefficientSupportedOpenBassTelescopeConeComparison_inclusion (a : Under
  R) :
    mappingConeInclusion ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f
      T).app a) ≫
        (boundedAboveFlatCoefficientSupportedOpenBassTelescopeConeComparison f T).app a =
      (boundedAboveFlatCoefficientSupportedOpenBassTelescopeGrading f T).app a :=
        mappingConeInclusion_desc _ _ _

omit [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left] in
/-- Genuine finite Model excision supplies the original telescope cone-to-fiber comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:226"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem
  boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction_coneFiber_isStableEquivalence
    (a : Under R) : IsStableEquivalence (mappingConeFiberComparison
      ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a)) := by
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i).obj a).space
    m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientSupportedOpenModelFunctor f T) a m
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T i).obj
    a).space m)
    :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T) a m
  exact Telescope.coneFiberComparison_isStableEquivalence
    (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassTransition f T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedFullOpenBassTransition f T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a)
      (boundedAboveFlatCoefficientSupportedOpenBassRestriction_transition f T i))
    (fun i ↦ boundedAboveFlatCoefficientSupportedOpenBassRestriction_coneFiber_isStableEquivalence
      f T i
      a)

variable [QuasiSeparatedSpace Q.left] [CompactSpace T]

/-- Actual finite cone stability passes to the same original telescope descent. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:250"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem boundedAboveFlatCoefficientSupportedOpenBassTelescopeConeComparison_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeConeComparison f
      T).app a)
      := by
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i).obj a).space
    m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientSupportedOpenModelFunctor f T) a m
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T i).obj
    a).space m)
    :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T) a m
  let : ∀ i m, T1Space (((boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T i).obj
    a).space
    m) :=
    fun i m ↦ modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientSupportedGradedOpenModelFunctor f T) a m
  exact Telescope.coneDesc_isStableEquivalence
    (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassTransition f T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedFullOpenBassTransition f T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T i).obj a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i).app a)
    (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassGrading f T i).app a)
    (fun i ↦ congrArg (fun η ↦ η.app a)
      (boundedAboveFlatCoefficientSupportedOpenBassRestriction_transition f T i))
    (fun i ↦ congrArg (fun η ↦ η.app a)
      (boundedAboveFlatCoefficientSupportedOpenBassGrading_transition f
      T i))
    (fun i ↦ (boundedAboveFlatCoefficientSupportedOpenBassGradingNull f T i).homotopy a)
    (fun i m s x ↦ boundedAboveFlatCoefficientSupportedOpenBassGradingNull_transition f T i a m s x)
    (fun i ↦ boundedAboveFlatCoefficientSupportedOpenBassConeComparison_isStableEquivalence f T i a)

/-- The same original restriction cone has no signed stable classes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:283"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem
  boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction_cone_stableGroup_subsingleton
    (a : Under R) (d : ℤ) : Subsingleton (stableHomotopyGroup
      (mappingCone ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a))
        d) :=
        by
  let j := (stableHomotopyFunctor d).map
    ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeConeComparison f T).app a)
  have hi : Function.Injective j :=
    ((ConcreteCategory.isIso_iff_bijective j).mp
      (boundedAboveFlatCoefficientSupportedOpenBassTelescopeConeComparison_isStableEquivalence f T a
        d)).injective
  exact ⟨fun x y ↦ hi
    ((boundedAboveFlatCoefficientSupportedGradedOpenBassTelescope_stableClass_eq_zero f T a d (j
      x)).trans
      (boundedAboveFlatCoefficientSupportedGradedOpenBassTelescope_stableClass_eq_zero f T a d (j
        y)).symm)⟩

/-- The actual original r-infinity is stable in every integer degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedOpenBassTelescope.lean:300"
  "adaptation"
    "Original graded Bass transitions, full telescope null and signed stable restriction"]
theorem boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction_isStableEquivalence
    (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f
      T).app a) :=
  isStableEquivalence_of_cone_stableGroup_subsingleton _
    (boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction_coneFiber_isStableEquivalence
      f T
      a)
    (boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction_cone_stableGroup_subsingleton
      f T
      a)

end AlgebraicGeometry.Scheme.Modules
