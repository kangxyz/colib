/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionLoopHomotopyEquiv
public import Colib.RingTheory.KTheory.Plus.ProjectiveQLoopComponentProduct

/-!
# Actual discrete K₀ times the original plus-certified completion model

Compose the genuine zero-component comparison with the already-proved
normalized original Q-loop component product. The plus factor is precisely
the original independently constructed StableCompletion.ZeroComponent, whose
stableZeroMap is already certified as a plus construction. The neutral slice
is exactly its standard original Q comparison and every first-coordinate label
is unchanged. No replacement plus model or higher-coherent splitting is used.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/KTheory/Plus/ProjectiveOriginalPlusProduct.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and original proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology
universe u
namespace ModuleCat.FiniteProjective

variable (R : Type u) [Ring R]

/-- The original discrete homotopical K₀ labels times the original plus-certified model. -/
abbrev OriginalKZeroPlusProduct :=
  (exactStructure.{u, u} Rᵐᵒᵖ).DiscreteKZero × StableCompletion.ZeroComponent R

/-- The exact standard zero-component comparison on the second product coordinate. -/
def originalPlusProductComponentMap :
    C(OriginalKZeroPlusProduct R,
      (exactStructure.{u, u} Rᵐᵒᵖ).DiscreteKZero ×
        (exactStructure.{u, u} Rᵐᵒᵖ).QLoopIdentityComponent) where
  toFun z := (z.1, StableCompletion.zeroCompletionToOriginalQLoops R z.2)
  continuous_toFun := continuous_fst.prodMk
    ((StableCompletion.zeroCompletionToOriginalQLoops R).continuous.comp continuous_snd)

/-- The genuine normalized product-to-original-loop homotopy equivalence. -/
def originalPlusProductToQLoopsHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (OriginalKZeroPlusProduct R)
      (Path (exactStructure.{u, u} Rᵐᵒᵖ).kBasepoint (exactStructure Rᵐᵒᵖ).kBasepoint) :=
  ((ContinuousMap.HomotopyEquiv.refl ((exactStructure.{u, u} Rᵐᵒᵖ).DiscreteKZero)).prodCongr
    (StableCompletion.zeroCompletionToOriginalQLoopsHomotopyEquiv R)).trans
      (exactStructure Rᵐᵒᵖ).qLoopComponentProductEquiv

/-- The full original Q-loop-to-K₀-times-original-plus homotopy equivalence. -/
def originalQLoopsPlusProductHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (Path (exactStructure.{u, u} Rᵐᵒᵖ).kBasepoint (exactStructure Rᵐᵒᵖ).kBasepoint)
      (OriginalKZeroPlusProduct R) :=
  (originalPlusProductToQLoopsHomotopyEquiv R).symm

/-- Its product-to-loop function uses the exact original standard zero map. -/
theorem originalPlusProductToQLoopsHomotopyEquiv_toFun :
    (originalPlusProductToQLoopsHomotopyEquiv R).toFun =
      (exactStructure Rᵐᵒᵖ).qLoopComponentProductEquiv.toFun.comp
        (originalPlusProductComponentMap R) := by
  apply ContinuousMap.ext
  intro z
  rfl

/-- The entire neutral slice is exactly the original standard zero-component comparison. -/
theorem originalPlusProductToQLoopsHomotopyEquiv_neutral
    (z : StableCompletion.ZeroComponent R) :
    originalPlusProductToQLoopsHomotopyEquiv R
      ((exactStructure Rᵐᵒᵖ).discreteKZeroIdentity, z) =
        (StableCompletion.zeroCompletionToOriginalQLoops R z).val :=
  (exactStructure Rᵐᵒᵖ).qLoopComponentProductEquiv_identity
    (StableCompletion.zeroCompletionToOriginalQLoops R z)

/-- The neutral product basepoint keeps the prescribed original standard comparison path. -/
def originalPlusProductBasepointPath :
    Path (originalPlusProductToQLoopsHomotopyEquiv R
      ((exactStructure Rᵐᵒᵖ).discreteKZeroIdentity, StableCompletion.zeroBase R))
      (Path.refl (exactStructure Rᵐᵒᵖ).kBasepoint) :=
  (completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ (StableCompletion.stageObject R 0)).cast
    (originalPlusProductToQLoopsHomotopyEquiv_neutral R (StableCompletion.zeroBase R)) rfl

/-- Every point of that basepoint track is the unchanged standard track. -/
theorem originalPlusProductBasepointPath_apply (t : unitInterval) :
    originalPlusProductBasepointPath R t =
      completionToOriginalQLoopsBasepointPath Rᵐᵒᵖ (StableCompletion.stageObject R 0) t := rfl

/-- Away from the neutral slice, the map is literal right concatenation with its representative. -/
theorem originalPlusProductToQLoopsHomotopyEquiv_of_ne
    (a : (exactStructure.{u, u} Rᵐᵒᵖ).DiscreteKZero)
    (ha : a ≠ (exactStructure Rᵐᵒᵖ).discreteKZeroIdentity)
    (z : StableCompletion.ZeroComponent R) :
    originalPlusProductToQLoopsHomotopyEquiv R (a, z) =
      (StableCompletion.zeroCompletionToOriginalQLoops R z).val.trans
        ((exactStructure Rᵐᵒᵖ).qLoopRepresentative a) :=
  (exactStructure Rᵐᵒᵖ).qLoopComponentProductEquiv_of_ne a ha
    (StableCompletion.zeroCompletionToOriginalQLoops R z)

/-- The inverse product coordinate is exactly the original continuous discrete K₀ classifier. -/
theorem originalQLoopsPlusProductHomotopyEquiv_label
    (γ : Path (exactStructure.{u, u} Rᵐᵒᵖ).kBasepoint (exactStructure Rᵐᵒᵖ).kBasepoint) :
    (originalQLoopsPlusProductHomotopyEquiv R γ).1 =
      (exactStructure Rᵐᵒᵖ).continuousLoopKZeroLabel γ :=
  (exactStructure Rᵐᵒᵖ).qLoopProductEquiv_label γ

/-- The exact standard canonical comparison has its unchanged positive completion label. -/
theorem originalQLoopsPlusProductHomotopyEquiv_comparison_label
    (x : ClassifyingSpace (GroupCompletionCategory Rᵐᵒᵖ)) :
    ((originalQLoopsPlusProductHomotopyEquiv R (originalQComparison Rᵐᵒᵖ x)).1).ofTopology =
      completionZerothHomotopyKZeroEquiv Rᵐᵒᵖ (ZerothHomotopy.mk x) := by
  rw [originalQLoopsPlusProductHomotopyEquiv_label]
  exact originalQComparison_kZero Rᵐᵒᵖ x

/-- Every original right-module stage has the positive numerator-minus-denominator coordinate. -/
theorem originalQLoopsPlusProductHomotopyEquiv_stage_label (n : ℕ) (P : IsoCategory Rᵐᵒᵖ) :
    ((originalQLoopsPlusProductHomotopyEquiv R
      (completionToOriginalQLoops Rᵐᵒᵖ (StableCompletion.stageObject R 0)
        (classifyingSpacePoint (completionPair Rᵐᵒᵖ (rankOnePower Rᵐᵒᵖ n) P)))).1).ofTopology =
      (exactStructure Rᵐᵒᵖ).kZeroObjectClass P.of /
        (exactStructure Rᵐᵒᵖ).kZeroObjectClass (rankOnePower Rᵐᵒᵖ n).of := by
  rw [originalQLoopsPlusProductHomotopyEquiv_label]
  exact completionToOriginalQLoops_stage_kZero R n P

end ModuleCat.FiniteProjective

attribute [colib_tag "COL-0606",
  colib_ref "quillen" "KTheory/Plus/ProjectiveOriginalPlusProduct.lean:48-129"
    "adaptation" "Actual product equivalence, neutral track, right concatenation and K-zero labels"]
  ModuleCat.FiniteProjective.originalPlusProductToQLoopsHomotopyEquiv
  ModuleCat.FiniteProjective.originalQLoopsPlusProductHomotopyEquiv
  ModuleCat.FiniteProjective.originalPlusProductToQLoopsHomotopyEquiv_neutral
  ModuleCat.FiniteProjective.originalPlusProductBasepointPath_apply
  ModuleCat.FiniteProjective.originalPlusProductToQLoopsHomotopyEquiv_of_ne
  ModuleCat.FiniteProjective.originalQLoopsPlusProductHomotopyEquiv_label
  ModuleCat.FiniteProjective.originalQLoopsPlusProductHomotopyEquiv_comparison_label
  ModuleCat.FiniteProjective.originalQLoopsPlusProductHomotopyEquiv_stage_label
