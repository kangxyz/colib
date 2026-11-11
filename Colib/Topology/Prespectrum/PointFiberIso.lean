/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.SuspensionLoopCounit
public import Colib.Topology.Prespectrum.FiberSequence

/-! # The actual point-to-spectrum fiber

The complete fiber path is retained as a based loop. Its actual isomorphism identifies
the original evaluation null-homotopy fiber lift, without replacing it by a stable class.
-/
@[expose] public noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped unitInterval
universe u v w
namespace Topology.LoopPrespectrum

/-- Retain the whole fiber path of the literal point-to-spectrum map as a based loop. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SuspensionLoopCounit.lean:90"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
def pointFiberInverse (E : LoopPrespectrum.{u}) :
    homotopyFiber (zeroHom pointPrespectrum E) ⟶ parameterLooping E where
  map n := {
    toFun z := {
      toFun := z.1.2
      continuous_toFun := z.1.2.continuous
      source' := z.2.1
      target' := z.2.2 }
    continuous_toFun := by
      apply Path.continuous_uncurry_iff.mp
      change Continuous (fun z :
        (homotopyFiber (zeroHom pointPrespectrum E)).space n × unitInterval ↦ z.1.1.2 z.2)
      fun_prop }
  map_point _n := by apply Path.ext; funext s; rfl
  comm _n _γ := by apply Path.ext; funext t; apply Path.ext; funext s; rfl

/-- The original loop-to-fiber inclusion is an isomorphism for the actual point source. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SuspensionLoopCounit.lean:107"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
def pointFiberIso (E : LoopPrespectrum.{u}) :
    parameterLooping E ≅ homotopyFiber (zeroHom pointPrespectrum E) where
  hom := homotopyFiberLoopInclusion (zeroHom pointPrespectrum E)
  inv := pointFiberInverse E
  hom_inv_id := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro γ
    apply Path.ext
    funext s
    rfl
  inv_hom_id := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    apply Prod.ext
    · change (PUnit.unit : PUnit.{u+1}) = _
      exact Subsingleton.elim _ _
    · apply ContinuousMap.ext
      intro s
      rfl

/-- The specified counit's whole-null fiber lift is exactly the original point-fiber map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/SuspensionLoopCounit.lean:133"
  "adaptation" "Original actual finite-stage topology and full all-point growth bounds."]
theorem loopEvaluationHomotopy_fiberLift (E : LoopPrespectrum.{u}) :
    homotopyFiberLift (zeroHom pointPrespectrum E) (zeroHom (parameterLooping E) pointPrespectrum)
      (loopEvaluationHomotopy E) = (pointFiberIso E).hom := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro γ
  apply Subtype.ext
  rfl

end Topology.LoopPrespectrum
