/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.Point
public import Colib.Topology.Prespectrum.MappingCone
public import Colib.Topology.Prespectrum.ParameterLooping

/-! # The original actual successor, counit and backward triangle

Only the selected original construction and exact triangle are migrated here.
No stability, connectivity or telescope comparison is assumed or claimed.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace Topology.LoopPrespectrum
/-- The actual reduced suspension carrier, using the original point and mapping cone. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/SuspensionLoopCounit.lean:31"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
def suspensionCone (E : LoopPrespectrum.{u}) : LoopPrespectrum.{u} :=
  mappingCone (zeroHom E pointPrespectrum)

/-- An actual map induces the original strict map of reduced suspension cones. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/SuspensionLoopCounit.lean:35"
  "adaptation" "Original strict map of the same reduced suspension cones."]
def suspensionConeMap {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    suspensionCone E ⟶ suspensionCone F :=
  mappingConeMap (A := Arrow.mk (zeroHom E pointPrespectrum))
    (B := Arrow.mk (zeroHom F pointPrespectrum))
    (Arrow.homMk f (𝟙 pointPrespectrum) (by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    rfl))

/-- Evaluation of a based parameter loop is a coherent zero homotopy, including structure time. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/SuspensionLoopCounit.lean:47"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
def loopEvaluationHomotopy (E : LoopPrespectrum.{u}) :
    Homotopy (zeroHom (parameterLooping E) pointPrespectrum ≫ zeroHom pointPrespectrum E)
      (zeroHom (parameterLooping E) E) where
  level n := ⟨fun z ↦ Path.toContinuousMap z.2 z.1, by fun_prop⟩
  at_zero _n γ := γ.source
  at_one _n γ := γ.target
  at_point _n _s := rfl
  comm _n _s _γ _t := rfl

/-- The actual counit evaluates the original suspension cylinder on the original loop. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/SuspensionLoopCounit.lean:57"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
def suspensionLoopCounit (E : LoopPrespectrum.{u}) :
    suspensionCone (parameterLooping E) ⟶ E :=
  mappingConeDesc (zeroHom (parameterLooping E) pointPrespectrum)
    (zeroHom pointPrespectrum E) (loopEvaluationHomotopy E)

end Topology.LoopPrespectrum

attribute [colib_tag "COL-0553"]
  Topology.LoopPrespectrum.suspensionLoopCounit
