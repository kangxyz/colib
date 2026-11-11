/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ArrowDiagrams
public import Colib.Topology.Prespectrum.ConeDescNaturality

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
namespace Topology.LoopPrespectrum
variable {C : Type u} [Category.{v} C]
variable {F G K : C ⥤ LoopPrespectrum.{w}} (a : F ⟶ G)

/-- The original component-arrow diagram followed by the actual quotient-cone functor. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/ConeDiagram.lean:26"
  "adaptation" "Original actual null/unit/null word and coefficient-natural maps"]
def mappingConeDiagram : C ⥤ LoopPrespectrum.{w} :=
  (ArrowDiagrams.toDiagram.obj (Arrow.mk a)) ⋙ mappingConeFunctor

end Topology.LoopPrespectrum
