/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.CharacteristicQuotient

/-!
# The original characteristic disk and sphere pair

The sphere and its inclusion use exactly the sup-norm coordinates of Mathlib's
classical characteristic maps. In dimension zero the disk has one point and the
sphere is empty. This boundary owner does not require cubical lifting machinery.

Adapted from `Quillen/Topology/CWComplex/CharacteristicPair.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

open Topology
noncomputable section
open Set Metric
namespace Topology.CWComplex

/-- The literal sphere boundary of the sup-norm characteristic disk. -/
abbrev CharacteristicSphere (n : ℕ) := ↥(sphere (0 : Fin n → ℝ) 1)

/-- The original inclusion of the characteristic sphere into the closed disk. -/
def characteristicSphereInclusion (n : ℕ) :
    C(CharacteristicSphere n, CharacteristicDisk n) :=
  ⟨fun z ↦ ⟨z.val, sphere_subset_closedBall z.property⟩,
    continuous_subtype_val.subtype_mk _⟩

@[simp] theorem characteristicSphereInclusion_val (n : ℕ) (z : CharacteristicSphere n) :
    (characteristicSphereInclusion n z).val = z.val := rfl

/-- The zero-dimensional characteristic disk has exactly one point. -/
@[instance_reducible] def characteristicDiskZeroUnique : Unique (CharacteristicDisk 0) where
  default := ⟨0, by simp⟩
  uniq _ := Subsingleton.elim _ _

/-- The literal zero-dimensional sphere is empty. -/
theorem characteristicSphere_zero_isEmpty : IsEmpty (CharacteristicSphere 0) :=
  inferInstance

end Topology.CWComplex
