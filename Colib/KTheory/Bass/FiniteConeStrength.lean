/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.FiniteConeLoopTopology
public import Colib.Topology.Prespectrum.LoopTranspose
public import Colib.KTheory.Bass.LoopStable

/-!
# Original loop strength on finite normalized cone stages

The original loop strength is stable on every diagram obtained by finite unlooped cones
followed by finite parameter looping of an actual Model diagram. All topology and growth
inputs come from the finite-cone closure theorem, with offset equal to the loop count.
The strength is unchanged, including its actual double-loop transpose. This supplies a
single finite-stage comparison, rather than tower transitions or their coherence.
-/
@[expose] public section
noncomputable section
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace KTheory.Bass.FiniteConeStrength
open FiniteConeTopology
variable {C : Type u} [Category.{v} C]

/-- The original single loop strength is stable at every finite normalized Model stage. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteConeStrength.lean:31"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem model_strength_stable (Q : C ⥤ Arrow (Arrow C)) (i j : ℕ)
    (M : C ⥤ WideSubcategory preservesZero.{w}) (X : C) :
    IsStableEquivalence (LoopStrength.strength Q
      (loopDiagram j (iterate Q i (M ⋙ prespectrumFunctor))) X) := by
  let F := iterate Q i (M ⋙ prespectrumFunctor)
  let : ∀ Y n, T1Space (((loopDiagram j F).obj Y).space n) := by
    intro Y n
    rw [loopDiagram_obj]
    exact modelLoopsIterateSpaceT1Space Q i j M Y n
  apply LoopStable.strength_stable Q (loopDiagram j F) j
  · intro Y n
    rw [loopDiagram_obj]
    exact modelLoopsIterate_point_homotopyExtensionProperty Q i j M Y n
  · intro Y n x k hk
    revert x
    rw [loopDiagram_obj]
    intro x
    exact modelLoopsIterate_homotopyGroup_subsingleton Q i j M Y n k hk x

end KTheory.Bass.FiniteConeStrength
