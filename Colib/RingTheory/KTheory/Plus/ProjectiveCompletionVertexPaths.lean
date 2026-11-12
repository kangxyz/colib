/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionLoops

/-! # The actual vertex paths of projective completion

These shared declarations retain `Quillen/KTheory/Plus/ProjectiveCompletionLoopKZero.lean:34-53`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Both the localized contraction and the
Q-loop label comparison use the same stored inverse-isomorphism edge and endpoint cast.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
universe u
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]

/-- The original vertex path, with only the exact realization-map endpoint equality inserted. -/
def completionQVertexPath (U : GroupCompletionCategory R) :
    Path (classifyingSpaceMapUniversal (localizedExtensionProjection R)
      (classifyingSpacePoint ((completionIdentityEntry R).obj U)))
      (classifyingSpacePoint (exactStructure R).qZero) :=
  (classifyingSpacePath ((completionIdentityProjectionIsoZero R).inv.app U)).symm.cast
    (classifyingSpaceMapUniversal_point (localizedExtensionProjection R) _) rfl

/-- The original fiber vertex has exactly the identity-extension source and original Q-edge path. -/
theorem completionQFiberPoint_vertex (U : GroupCompletionCategory R) :
    completionQFiberPoint R U = HomotopyFiber.pointWithPath
      (classifyingSpaceMapUniversal (localizedExtensionProjection R))
      (classifyingSpacePoint ((completionIdentityEntry R).obj U))
      (classifyingSpacePoint (exactStructure R).qZero) (completionQVertexPath R U) := by
  apply Subtype.ext
  apply Prod.ext
  · exact completionToOriginalQHomotopyFiber_vertex_source R U
  · apply ContinuousMap.ext
    intro t
    exact completionToOriginalQHomotopyFiber_vertex_path R U t

end ModuleCat.FiniteProjective
