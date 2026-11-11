/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.Homotopy
public import Colib.Util.References

/-!
# Coefficient-natural null tracks of prespectrum diagrams

This is the original whole-track structure from Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Its naturality retains the same homotopy
time at every coefficient map. Isomorphism transport is not part of this minimal closure.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v w
namespace Topology.LoopPrespectrum
variable {C : Type u} [Category.{v} C]
    {F G K : C ⥤ LoopPrespectrum.{w}} (a : F ⟶ G) (b : G ⟶ K)

/-- Whole original null tracks which commute with every coefficient at the same time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/DiagramNullHomotopy.lean:28-34"
  "adaptation" "Original complete null tracks and same-time coefficient naturality"]
structure DiagramNullHomotopy where
  /-- The specified based whole null track at each original coefficient object. -/
  homotopy (X : C) : Homotopy (a.app X ≫ b.app X) (zeroHom (F.obj X) (K.obj X))
  /-- The complete tracks commute with the unchanged coefficient maps. -/
  naturality : ∀ {X Y} (f : X ⟶ Y) n r x,
    (K.map f).map n ((homotopy X).level n (r, x)) =
      (homotopy Y).level n (r, (F.map f).map n x)

end Topology.LoopPrespectrum
