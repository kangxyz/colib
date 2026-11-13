/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.PathComponent
public import Mathlib.Topology.Homotopy.Equiv

/-! # Restricting genuine homotopy equivalences to actual path components -/
open Topology

/-! Implementation source: `Quillen/Topology/HomotopyEquiv/PathComponent.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section
universe u v
namespace Topology
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Restrict both original maps and inverse homotopies to their actual components.
The specified basepoint need only be joined to the original forward image. -/
def pathComponentHomotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y)
    (x : X) (y : Y) (h : Joined (e x) y) :
    ContinuousMap.HomotopyEquiv (pathComponent x) (pathComponent y) := by
  let f : C(pathComponent x, pathComponent y) :=
    { toFun z := ⟨e z.val, h.symm.trans (z.property.map e.continuous)⟩
      continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _ }
  let g : C(pathComponent y, pathComponent x) :=
    { toFun z := ⟨e.invFun z.val,
        (show Joined x (e.invFun (e x)) from ⟨(e.left_inv.some.evalAt x).symm⟩).trans
          ((h.map e.invFun.continuous).trans (z.property.map e.invFun.continuous))⟩
      continuous_toFun := (e.invFun.continuous.comp continuous_subtype_val).subtype_mk _ }
  refine { toFun := f, invFun := g, left_inv := ⟨?_⟩, right_inv := ⟨?_⟩ }
  · let H := e.left_inv.some
    exact
      { toFun z := ⟨H (z.1, z.2.val),
          path_mem_pathComponent (H.evalAt z.2.val) (g (f z.2)).property z.1⟩
        continuous_toFun := (H.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
        map_zero_left z := Subtype.ext (H.apply_zero z.val)
        map_one_left z := Subtype.ext (H.apply_one z.val) }
  · let H := e.right_inv.some
    exact
      { toFun z := ⟨H (z.1, z.2.val),
          path_mem_pathComponent (H.evalAt z.2.val) (f (g z.2)).property z.1⟩
        continuous_toFun := (H.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
        map_zero_left z := Subtype.ext (H.apply_zero z.val)
        map_one_left z := Subtype.ext (H.apply_one z.val) }

/-- The component equivalence retains precisely the original forward map. -/
@[simp]
theorem pathComponentHomotopyEquiv_val (e : ContinuousMap.HomotopyEquiv X Y)
    (x : X) (y : Y) (h : Joined (e x) y) (z : pathComponent x) :
    (pathComponentHomotopyEquiv e x y h z).val = e z.val := rfl

/-- The component inverse retains precisely the original inverse map. -/
@[simp]
theorem pathComponentHomotopyEquiv_symm_val (e : ContinuousMap.HomotopyEquiv X Y)
    (x : X) (y : Y) (h : Joined (e x) y) (z : pathComponent y) :
    ((pathComponentHomotopyEquiv e x y h).symm z).val = e.invFun z.val := rfl

end Topology
