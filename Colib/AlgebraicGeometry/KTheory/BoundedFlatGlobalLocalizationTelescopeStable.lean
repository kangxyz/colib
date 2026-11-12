/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalOpenTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalLocalizationEquivalence
public import Colib.KTheory.Bass.ModelDiagramConnectivity
public import Colib.Topology.Prespectrum.TelescopeStableEquivalence
/-! # Original finite and global telescope restriction stability -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

namespace SupportedTelescope

/-- The actual finite restriction is stable by its exact categorical inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationTelescopeStable.lean:28"
  "adaptation" "Original exact inverse yields finite and whole telescope restriction stability"]
theorem finiteRestriction_isStableEquivalence (i : ℕ) (a : Under R) :
    IsStableEquivalence ((finiteRestriction f i).app a) :=
  supportedRowRestriction_iterate_isStableEquivalence f (laurentUnderSquareFunctor R) i a

/-- The actual natural telescope restriction is pointwise a stable equivalence. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationTelescopeStable.lean:33"
  "adaptation" "Original exact inverse yields finite and whole telescope restriction stability"]
theorem telescopeRestriction_isStableEquivalence (a : Under R) :
    IsStableEquivalence ((telescopeRestriction f).app a) := by
  let : ∀ i n, T1Space (((globalDiagram f i).obj a).space n) :=
    fun i n => modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (supportedRow f) a n
  let : ∀ i n, T1Space (((boundedAboveFlatCoefficientSupportedBassDiagram f i).obj a).space n) :=
    fun i n => modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientSupportedModelFunctor f) a n
  exact Telescope.map_isStableEquivalence
    (fun i => (globalDiagram f i).obj a) (fun i => (globalTransition f i).app a)
    (fun i => (boundedAboveFlatCoefficientSupportedBassDiagram f i).obj a)
    (fun i => (boundedAboveFlatCoefficientSupportedBassTransition f i).app a)
    (fun i => (finiteRestriction f i).app a)
    (fun i => congrArg (fun η => η.app a) (finiteRestriction_transition f i))
    (fun i => finiteRestriction_isStableEquivalence f i a)


end SupportedTelescope

namespace OpenTelescope

/-- The actual finite restriction is stable by its exact categorical inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationTelescopeStable.lean:55"
  "adaptation" "Original exact inverse yields finite and whole telescope restriction stability"]
theorem finiteRestriction_isStableEquivalence (i : ℕ) (a : Under R) :
    IsStableEquivalence ((finiteRestriction f i).app a) :=
  openRowRestriction_iterate_isStableEquivalence f (laurentUnderSquareFunctor R) i a

/-- The actual natural telescope restriction is pointwise a stable equivalence. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationTelescopeStable.lean:60"
  "adaptation" "Original exact inverse yields finite and whole telescope restriction stability"]
theorem telescopeRestriction_isStableEquivalence (a : Under R) :
    IsStableEquivalence ((telescopeRestriction f).app a) := by
  let : ∀ i n, T1Space (((globalDiagram f i).obj a).space n) :=
    fun i n => modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (openRow f) a n
  let : ∀ i n, T1Space (((boundedAboveFlatCoefficientOpenBassDiagram f i).obj a).space n) :=
    fun i n => modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedAboveFlatCoefficientOpenModelFunctor f) a n
  exact Telescope.map_isStableEquivalence
    (fun i => (globalDiagram f i).obj a) (fun i => (globalTransition f i).app a)
    (fun i => (boundedAboveFlatCoefficientOpenBassDiagram f i).obj a)
    (fun i => (boundedAboveFlatCoefficientOpenBassTransition f i).app a)
    (fun i => (finiteRestriction f i).app a)
    (fun i => congrArg (fun η => η.app a) (finiteRestriction_transition f i))
    (fun i => finiteRestriction_isStableEquivalence f i a)


end OpenTelescope

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

