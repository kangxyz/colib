/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionLoopNaturality
public import Colib.RingTheory.KTheory.Plus.ProjectiveCompletionZeroLoops

/-!
# The standard completion-loop homotopy on the actual zero components

Every point of the ambient naturality homotopy stays in the component of its
initial loop. The component restriction therefore has exactly the standard
ambient values and endpoints. The specified comparison and ring-change basepoint
paths remain separate data; this homotopy is not asserted to fix the loop unit.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/KTheory/Plus/ProjectiveCompletionZeroLoopNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Topology

universe u

namespace ModuleCat.FiniteProjective.StableCompletion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  rightBaseChangeCoreMonoidal

variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

/-- Actual normalized Q base change restricted to the components of the constant loops. -/
def zeroOriginalQLoopsBaseChangeMap :
    C(OriginalQLoopsZeroComponent R, OriginalQLoopsZeroComponent S) :=
  pathComponentMap
    (basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
      (completionNormalizedQ_basepoint f))
    (Path.refl (classifyingSpacePoint (exactStructure Rᵐᵒᵖ).qZero))
    (Path.refl (classifyingSpacePoint (exactStructure Sᵐᵒᵖ).qZero))
    (by rw [basedLoopMap_refl])

/-- The component map retains the literal original normalized Q loop map. -/
@[simp] theorem zeroOriginalQLoopsBaseChangeMap_val (x : OriginalQLoopsZeroComponent R) :
    (zeroOriginalQLoopsBaseChangeMap f x).val =
      basedLoopMap (classifyingSpaceMap (rightBaseChangeExact f).normalizedQ).hom
        (completionNormalizedQ_basepoint f) x.val := rfl

/-- Restrict the genuine all-points naturality homotopy to the actual zero components. -/
def zeroCompletionToOriginalQLoopsBaseChangeHomotopy :
    ((zeroOriginalQLoopsBaseChangeMap f).comp (zeroCompletionToOriginalQLoops R)).Homotopy
    ((zeroCompletionToOriginalQLoops S).comp (zeroCompletionBaseChangeMap f)) where
  toFun z := ⟨completionToOriginalQLoopsBaseChangeHomotopy f (z.1, z.2.val),
    path_mem_pathComponent
      ((completionToOriginalQLoopsBaseChangeHomotopy f).evalAt z.2.val)
      (zeroOriginalQLoopsBaseChangeMap f (zeroCompletionToOriginalQLoops R z.2)).property z.1⟩
  continuous_toFun := ((completionToOriginalQLoopsBaseChangeHomotopy f).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left z :=
    Subtype.ext ((completionToOriginalQLoopsBaseChangeHomotopy f).apply_zero z.val)
  map_one_left z :=
    Subtype.ext ((completionToOriginalQLoopsBaseChangeHomotopy f).apply_one z.val)

/-- Every point of the restricted homotopy is the specified standard ambient homotopy point. -/
@[simp] theorem zeroCompletionToOriginalQLoopsBaseChangeHomotopy_val
    (t : unitInterval) (x : ZeroComponent R) :
    (zeroCompletionToOriginalQLoopsBaseChangeHomotopy f (t, x)).val =
      completionToOriginalQLoopsBaseChangeHomotopy f (t, x.val) := rfl

end ModuleCat.FiniteProjective.StableCompletion

attribute [colib_tag "COL-0602",
  colib_ref "quillen" "KTheory/Plus/ProjectiveCompletionZeroLoopNaturality.lean"
    "adaptation" "Ordinary ring-change homotopy of the unchanged original component comparison"]
  ModuleCat.FiniteProjective.StableCompletion.zeroCompletionToOriginalQLoopsBaseChangeHomotopy
