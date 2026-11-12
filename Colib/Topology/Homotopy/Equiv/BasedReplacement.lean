/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.Equiv.Based
public import Colib.Topology.Homotopy.RelativeInverse

/-!
# Based inverses for original equivalences at cofibrant points

An actual homotopy equivalence carrying a specified cofibrant point to another
has a based homotopy inverse. The original forward map is unchanged; the two
inverse homotopies are made relative to the specified points by the proved
relative-inverse theorem.
-/

open Topology TopCat

/-! Implementation source: `Quillen/Topology/HomotopyEquiv/BasedReplacement.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped Topology unitInterval

universe u
namespace Topology.BasedHomotopyEquiv

/-- Correct the inverse and inverse homotopies, retaining the original forward
map of a homotopy equivalence between spaces with cofibrant chosen points. -/
def ofHomotopyEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (e : ContinuousMap.HomotopyEquiv X Y) (h : e x = y)
    (hx : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x)))
    (hy : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} y))) : BasedHomotopyEquiv x y := by
  let i := TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x)
  let j := TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} y)
  have w : i ≫ TopCat.ofHom e.toFun = j := by
    ext a
    exact h
  let result := homotopyExtensionProperty_exists_relative_inverse hx hy e w
  let r := result.choose
  have hr : j ≫ r = i := result.choose_spec.1
  let L := result.choose_spec.2.1.some
  let R := result.choose_spec.2.2.some
  exact {
    toMap := e.toFun
    invMap := r.hom
    map_point := h
    inv_point := ConcreteCategory.congr_hom hr PUnit.unit
    leftHomotopy := L.toHomotopy
    rightHomotopy := R.toHomotopy
    left_fixed := fun t ↦ L.eq_snd t ⟨PUnit.unit, rfl⟩
    right_fixed := fun t ↦ R.eq_snd t ⟨PUnit.unit, rfl⟩ }

@[simp]
theorem ofHomotopyEquiv_toMap {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (e : ContinuousMap.HomotopyEquiv X Y) (h : e x = y)
    (hx : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x)))
    (hy : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} y))) :
    (ofHomotopyEquiv e h hx hy).toMap = e.toFun := rfl

end Topology.BasedHomotopyEquiv
