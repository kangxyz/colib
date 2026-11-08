/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.HomotopyLoop
public import Colib.Topology.Prespectrum.MappingCone

/-! # The actual cone-null self-track transition

The original reduced cone nullhomotopy supplies the complete conjugating path.
No chosen filler or stable-equivalence premise is added.

Implementation provenance: `Quillen/Topology/Prespectrum/HomotopyLoop.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`, final three declarations.
The cone-independent null-loop construction is already native in `HomotopyLoop`.
-/
@[expose] public noncomputable section
open CategoryTheory
open scoped unitInterval
universe u
namespace Topology.LoopPrespectrum
variable {E F G : LoopPrespectrum.{u}}

/-- The cone nullhomotopy transports a self-homotopy of the original comparison to a based loop. -/
def mappingConeLoopTransition (f : E ⟶ F) (H : Homotopy f f) : E ⟶ parameterLooping (mappingCone f)
  :=
  (H.postcomp (mappingConeInclusion f)).nullLoopMap (mappingConeHomotopy f)

/-- The entire original loop remains the explicitly concatenated homotopy. -/
theorem mappingConeLoopTransition_apply (f : E ⟶ F) (H : Homotopy f f)
    (n : ℕ) (x : E.space n) (s : unitInterval) :
    Path.toContinuousMap ((mappingConeLoopTransition f H).map n x) s =
      ((H.postcomp (mappingConeInclusion f)).conjugateToZero (mappingConeHomotopy f)).level n (s,x)
        := rfl

/--
A self-homotopy along a specified original source leg yields the concrete cone-loop transition.
-/
def mappingConeLoopTransitionAlong (f : E ⟶ F) (a : G ⟶ E)
    (H : Homotopy (a ≫ f) (a ≫ f)) : G ⟶ parameterLooping (mappingCone f) :=
  (H.postcomp (mappingConeInclusion f)).nullLoopMap
    (Homotopy.precomp a (mappingConeHomotopy f))

attribute [colib_ref "quillen" "Topology/Prespectrum/HomotopyLoop.lean"
  "adaptation" "Actual cone-null track, full evaluation and original source-leg transport"]
  mappingConeLoopTransition mappingConeLoopTransition_apply mappingConeLoopTransitionAlong

end Topology.LoopPrespectrum
