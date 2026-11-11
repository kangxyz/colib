/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.ConeDiagram

/-! # Original coefficient-natural null/unit/null seed word

Only the original whole-word construction and its same-time naturality are selected.
No comparison under Bass, stability or telescope statement is assumed here.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.PushoutCofiberSquare
variable {C : Type u} [Category.{v} C]
variable {F₀ F₁ : C ⥤ LoopPrespectrum.{w}} (f : F₀ ⟶ F₁)

/-- Original cone inclusions as a coefficient-natural transformation. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/PushoutCofiberSquare.lean:32"
  "adaptation" "Original actual null/unit/null word and coefficient-natural maps"]
def coneInclusion : F₁ ⟶ mappingConeDiagram f where
  app X := mappingConeInclusion (f.app X)
  naturality X Y k := (mappingConeInclusionSquare
    (Arrow.homMk (f := Arrow.mk (f.app X)) (g := Arrow.mk (f.app Y))
      (F₀.map k) (F₁.map k) (f.naturality k))).w

end KTheory.Bass.PushoutCofiberSquare
