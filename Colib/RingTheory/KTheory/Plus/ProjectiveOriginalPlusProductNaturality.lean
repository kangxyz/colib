/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Plus.ProjectiveOriginalPlusProduct
public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionZeroLoopNaturality

/-!
# Ordinary base-change naturality of the original K₀-times-plus product

Combine the actual normalized loop-product naturality homotopy with the
already-proved ordinary homotopy for the exact standard zero-component map.
The discrete coordinate is the original K₀ map. No naturality of chosen
inverses, strict representative section, multiplicative splitting, or higher
coherence is asserted.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/KTheory/Plus/ProjectiveOriginalPlusProductNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and original proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace ModuleCat.FiniteProjective

variable {R S : Type u} [Ring R] [Ring S]

/-- The original K₀ map and original plus-model ring-change map on the two factors. -/
def originalPlusProductBaseChangeMap (f : R →+* S) :
    C(OriginalKZeroPlusProduct R, OriginalKZeroPlusProduct S) where
  toFun z := ((rightBaseChangeExact f).discreteKZeroMap z.1, zeroCompletionBaseChangeMap f z.2)
  continuous_toFun := by
    have hk : Continuous (rightBaseChangeExact f).discreteKZeroMap :=
      continuous_of_discreteTopology
    exact (hk.comp continuous_fst).prodMk
      ((zeroCompletionBaseChangeMap f).continuous.comp continuous_snd)

/-- The original zero-map naturality homotopy, placed inside the target normalized product. -/
def originalPlusProductNaturalityCorrection (f : R →+* S) :
    (((exactStructure Sᵐᵒᵖ).qLoopComponentProductEquiv.toFun.comp
      (loopComponentProductChange (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
        (rightBaseChangeExact f).normalizedQ_map_point
        (rightBaseChangeExact f).discreteKZeroMap)).comp
          (originalPlusProductComponentMap R)).Homotopy
      ((originalPlusProductToQLoopsHomotopyEquiv S).toFun.comp
        (originalPlusProductBaseChangeMap f)) where
  toFun z := (exactStructure Sᵐᵒᵖ).qLoopComponentProductEquiv
    ((rightBaseChangeExact f).discreteKZeroMap z.2.1,
      StableCompletion.zeroCompletionToOriginalQLoopsBaseChangeHomotopy f (z.1, z.2.2))
  continuous_toFun := by
    apply (exactStructure Sᵐᵒᵖ).qLoopComponentProductEquiv.continuous.comp
    have hk : Continuous (rightBaseChangeExact f).discreteKZeroMap :=
      continuous_of_discreteTopology
    exact (hk.comp (continuous_fst.comp continuous_snd)).prodMk
        ((StableCompletion.zeroCompletionToOriginalQLoopsBaseChangeHomotopy f).continuous.comp
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  map_zero_left z := by
    rw [(StableCompletion.zeroCompletionToOriginalQLoopsBaseChangeHomotopy f).apply_zero]
    rfl
  map_one_left z := by
    rw [(StableCompletion.zeroCompletionToOriginalQLoopsBaseChangeHomotopy f).apply_one,
      originalPlusProductToQLoopsHomotopyEquiv_toFun]
    rfl

/-- Unital ring change commutes with the actual original product up to ordinary homotopy. -/
theorem originalPlusProductToQLoopsHomotopyEquiv_naturality (f : R →+* S) :
    ((basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
      (rightBaseChangeExact f).normalizedQ_map_point).comp
        (originalPlusProductToQLoopsHomotopyEquiv R).toFun).Homotopic
      ((originalPlusProductToQLoopsHomotopyEquiv S).toFun.comp
        (originalPlusProductBaseChangeMap f)) := by
  rw [originalPlusProductToQLoopsHomotopyEquiv_toFun R, ← ContinuousMap.comp_assoc]
  exact ((rightBaseChangeExact f).qLoopComponentProductEquiv_naturality.comp
    (ContinuousMap.Homotopic.refl (originalPlusProductComponentMap R))).trans
      ⟨originalPlusProductNaturalityCorrection f⟩

end ModuleCat.FiniteProjective

attribute [colib_tag "COL-0606",
  colib_ref "quillen" "KTheory/Plus/ProjectiveOriginalPlusProductNaturality.lean:71-80"
    "adaptation" "Ordinary product-to-loop naturality for the original ring-change maps"]
  ModuleCat.FiniteProjective.originalPlusProductToQLoopsHomotopyEquiv_naturality
