/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.SuspensionLoopUnit
public import Colib.KTheory.Bass.ModelDiagramSuccessor

/-! # The original actual successor, counit and backward triangle

Only the selected original construction and exact triangle are migrated here.
No stability, connectivity or telescope comparison is assumed or claimed.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.ModelZigzagSequentialization
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (M : C ⥤ WideSubcategory preservesZero.{w}) (X : C)

/-- The original finite Bass vertices, before any loop-normalized stage comparison. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelZigzagSequentialization.lean:36"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
abbrev vertex (n : ℕ) : LoopPrespectrum.{w} :=
  (((strictDiagramIterate Q n).obj (M ⋙ prespectrumFunctor)).obj X)

/-- The literal looped suspension of the next original vertex. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelZigzagSequentialization.lean:40"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
abbrev suspendedVertex (n : ℕ) : LoopPrespectrum.{w} :=
  parameterLooping (suspensionCone (vertex Q M X (n + 1)))

/-- The canonical original backward leg, with the forward cone-cylinder orientation. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/ModelZigzagSequentialization.lean:44"
  "adaptation" "Original actual suspension evaluation and backward triangle"]
abbrev unit (n : ℕ) : vertex Q M X (n + 1) ⟶ suspendedVertex Q M X n :=
  suspensionLoopUnit (vertex Q M X (n + 1))

end KTheory.Bass.ModelZigzagSequentialization
