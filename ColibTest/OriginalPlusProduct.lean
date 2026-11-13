/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Plus.ProjectiveOriginalPlusProductNaturality

/-!
# Independent original K₀-times-BGL-plus product client

Consume both genuine inverse homotopies, the exact neutral slice, the already
proved plus certificate for the unchanged second factor, and an actual
ordinary base-change homotopy. No arbitrary-model uniqueness or higher
coherence of inverse choices is claimed.
-/

@[expose] public section
noncomputable section
open CategoryTheory Topology ModuleCat.FiniteProjective
open scoped Topology
universe u
namespace Consumer.OriginalPlusProduct

variable (R : Type u) [Ring R]

/-- Decomposing and reconstructing an original Q loop has an actual inverse path. -/
def recoverOriginalLoop
    (γ : Path (exactStructure.{u, u} Rᵐᵒᵖ).kBasepoint (exactStructure Rᵐᵒᵖ).kBasepoint) :
    Path ((originalQLoopsPlusProductHomotopyEquiv R).invFun
      (originalQLoopsPlusProductHomotopyEquiv R γ)) γ :=
  (originalQLoopsPlusProductHomotopyEquiv R).left_inv.some.evalAt γ

/-- Reconstructing and decomposing the original product has the other actual inverse path. -/
def recoverOriginalProduct (z : OriginalKZeroPlusProduct R) :
    Path (originalQLoopsPlusProductHomotopyEquiv R
      ((originalQLoopsPlusProductHomotopyEquiv R).invFun z)) z :=
  (originalQLoopsPlusProductHomotopyEquiv R).right_inv.some.evalAt z

/-- The second factor remains the target of the actual original ring-specific plus construction. -/
theorem original_plus_certificate :
    IsPlusConstruction.{u, u + 1, u + 1} (StableCompletion.stableZeroMap R)
      (StableCompletion.basepointPath R) (StableCompletion.stableElementaryPiOneSubgroup R) :=
  StableCompletion.stableZeroMap_isPlusConstruction R

/-- The neutral slice is exactly the accepted original standard map, for every factor point. -/
theorem original_neutral_slice (z : StableCompletion.ZeroComponent R) :
    (originalQLoopsPlusProductHomotopyEquiv R).invFun
      ((exactStructure Rᵐᵒᵖ).discreteKZeroIdentity, z) =
        (StableCompletion.zeroCompletionToOriginalQLoops R z).val :=
  originalPlusProductToQLoopsHomotopyEquiv_neutral R z

variable {R} {S : Type u} [Ring S]

/-- A chosen witness of the actual ordinary ring-change homotopy, with both exact endpoint maps. -/
def originalRingChangeHomotopy (f : R →+* S) :
    ((basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
      (rightBaseChangeExact f).normalizedQ_map_point).comp
        (originalPlusProductToQLoopsHomotopyEquiv R).toFun).Homotopy
      ((originalPlusProductToQLoopsHomotopyEquiv S).toFun.comp
        (originalPlusProductBaseChangeMap f)) :=
  (originalPlusProductToQLoopsHomotopyEquiv_naturality f).some

end Consumer.OriginalPlusProduct
